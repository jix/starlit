//! Parser for the DIMACS CNF file format.
use std::io::{BufReader, Read};

use thiserror::Error;

use crate::lit::{Lit, Var};

use super::{TokenKind, Tokenizer};

/// Error while parsing a DIMACS CNF file.
#[derive(Error, Debug)]
pub enum ParseError {
    /// Error while parsing an input line.
    #[error("{line}: {message}")]
    ParseError {
        /// Line number where an error was encountered.
        line: usize,
        /// Description of the encountered error
        message: String,
    },
    /// IO error while reading the input file.
    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

/// Header data of a DIMACS CNF file.
///
/// Contains the number of variables and clauses. This parser also supports partial headers that
/// omit either the clause count or both fields.
#[derive(Copy, Clone, Default, Debug)]
pub struct Header {
    /// Upper bound on the number of variables present in the formula.
    pub var_count: Option<usize>,
    /// Number of clauses present in the formula.
    pub clause_count: Option<usize>,
}

/// Parser for the DIMACS CNF file format.
pub struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
    header: Option<Header>,
    parsed_clauses: usize,
    max_clause_count: usize,
    max_var_count: i64,
    clause: Vec<Lit>,
}

macro_rules! parse_error {
    ($self:ident, $token:ident,$($args:expr),*) => {
        let err = ParseError::ParseError {
            line: $token.line,
            message: format!($($args),*),
        };
        $self.tokenizer.check_io_error()?;
        return Err(err);
    };
}

impl<'a> Parser<'a> {
    /// Initialize a [`Parser`] from a [`Tokenizer`].
    pub fn new(tokenizer: Tokenizer<'a>) -> Self {
        Parser {
            tokenizer,
            header: None,
            parsed_clauses: 0,
            max_clause_count: usize::MAX,
            max_var_count: Var::MAX_DIMACS as i64,
            clause: vec![],
        }
    }

    /// Initialize a [`Parser`] from a [`BufReader`].
    pub fn from_buf_reader(buf_reader: BufReader<impl Read + 'a>) -> Self {
        Self::new(Tokenizer::from_buf_reader(buf_reader))
    }

    /// Initialize a [`Parser`] with an underlying [`Read`] instance.
    ///
    /// If the [`Read`] instance is a [`BufReader`], it is better to use
    /// [`from_buf_reader`][Self::from_buf_reader] to avoid unnecessary copying of the read data.
    pub fn from_read(read: impl Read + 'a) -> Self {
        Self::new(Tokenizer::from_read(read))
    }

    fn parse_header(&mut self) -> Result<Header, ParseError> {
        let mut header = Header::default();
        let mut token = self.tokenizer.current_token();
        if token.bytes != "cnf" {
            parse_error!(self, token, "unexpected {}, expected \"cnf\"", token);
        }
        self.tokenizer.advance();
        token = self.tokenizer.current_token();
        match token.kind {
            TokenKind::Newline => {
                self.tokenizer.advance();
                return Ok(header);
            }
            TokenKind::Int if token.value >= 0 && token.value <= (Var::MAX_VAR_COUNT as i64) => {
                header.var_count = Some(token.value as usize);
                self.tokenizer.advance();
            }
            TokenKind::Int | TokenKind::BigInt => {
                let failure = if token.is_negative() {
                    "invalid"
                } else {
                    "unsupported"
                };
                parse_error!(self, token, "{} variable count {}", failure, token);
            }
            _ => {
                parse_error!(
                    self,
                    token,
                    "unexpected {}, expected variable count or end of line",
                    token
                );
            }
        }
        token = self.tokenizer.current_token();
        match token.kind {
            TokenKind::Newline => {
                self.tokenizer.advance();
                return Ok(header);
            }
            TokenKind::Int if token.value >= 0 && token.value as u64 <= usize::MAX as u64 => {
                header.clause_count = Some(token.value as usize);
                self.tokenizer.advance();
            }
            TokenKind::Int | TokenKind::BigInt => {
                let failure = if token.is_negative() {
                    "invalid"
                } else {
                    "unsupported"
                };
                parse_error!(self, token, "{} clause count {}", failure, token);
            }
            _ => {
                parse_error!(
                    self,
                    token,
                    "unexpected {}, expected clause count or end of line",
                    token
                );
            }
        }
        token = self.tokenizer.current_token();
        match token.kind {
            TokenKind::Newline => {
                self.tokenizer.advance();
                Ok(header)
            }
            _ => {
                parse_error!(self, token, "unexpected {}, expected end of line", token);
            }
        }
    }

    /// Parse and return the header of a DIMACS CNF file.
    ///
    /// This caches the result and can be called at any point during parsing.
    pub fn header(&mut self) -> Result<Option<Header>, ParseError> {
        if self.header.is_none() {
            loop {
                let token = self.tokenizer.current_token();
                match token.kind {
                    TokenKind::Comment | TokenKind::Newline => self.tokenizer.advance(),
                    TokenKind::Word
                        if token.bytes == "p"
                            && self.clause.is_empty()
                            && self.parsed_clauses == 0
                            && self.header.is_none() =>
                    {
                        self.tokenizer.advance();
                        let header = self.parse_header()?;

                        if let Some(var_count) = header.var_count {
                            self.max_var_count = var_count as i64;
                        }
                        if let Some(clause_count) = header.clause_count {
                            self.max_clause_count = clause_count;
                        }
                        self.header = Some(header);
                    }
                    _ => break,
                }
            }
        }

        Ok(self.header)
    }

    /// Parse and return the next clause.
    ///
    /// Returns `Ok<None>` on end of file.
    pub fn next_clause(&mut self) -> Result<Option<&[Lit]>, ParseError> {
        self.clause.clear();

        if self.parsed_clauses == 0 {
            self.header()?;
        }

        loop {
            let mut token = self.tokenizer.current_token();
            match token.kind {
                TokenKind::Comment | TokenKind::Newline => self.tokenizer.advance(),
                TokenKind::EndOfFile if self.clause.is_empty() => {
                    if let Some(header) = &self.header {
                        if let Some(clause_count) = header.clause_count {
                            if self.parsed_clauses != clause_count {
                                parse_error!(
                                    self,
                                    token,
                                    "unexpected end of file, expected further clauses"
                                );
                            }
                        }
                    }
                    return Ok(None);
                }
                TokenKind::Int if token.value == 0 => {
                    self.tokenizer.advance();
                    token = self.tokenizer.current_token();
                    if !matches!(token.kind, TokenKind::Newline | TokenKind::EndOfFile) {
                        parse_error!(self, token, "unexpected {}, expected end of line", token);
                    }
                    self.parsed_clauses += 1;
                    if self.parsed_clauses > self.max_clause_count {
                        parse_error!(self, token, "unexpected clause, expected end of file");
                    }
                    self.tokenizer.advance();
                    return Ok(Some(&self.clause));
                }
                TokenKind::Int if token.value.abs() <= self.max_var_count => {
                    self.clause.push(Lit::from_dimacs(token.value as isize));
                    self.tokenizer.advance()
                }
                TokenKind::Int | TokenKind::BigInt => {
                    let failure = if matches!(
                        self.header,
                        Some(Header {
                            var_count: Some(_),
                            ..
                        })
                    ) {
                        "specified"
                    } else {
                        "supported"
                    };
                    parse_error!(self, token, "literal {} outside {} range", token, failure);
                }
                _ => {
                    if self.clause.is_empty() && self.parsed_clauses == 0 && self.header.is_none() {
                        parse_error!(
                            self,
                            token,
                            "unexpected {}, expected literal or file header",
                            token
                        );
                    } else {
                        parse_error!(self, token, "unexpected {}, expected literal", token);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    macro_rules! clause {
        ($($lit:expr),*) => {
            vec![$(Lit::from_dimacs($lit)),*].as_ref()
        };
    }

    macro_rules! assert_matches {
        ($value:expr, $matches:pat) => {
            let value = $value;
            assert!(
                matches!(&value, &$matches),
                "{:?} does not match {}",
                value,
                stringify!($matches)
            );
        };
    }

    #[test]
    fn empty() -> Result<()> {
        let mut parser = Parser::from_read("".as_bytes());

        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn headerless() -> Result<()> {
        let mut parser = Parser::from_read("1 2 -3 0\n4 5 0\n-6 0\n0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4, 5]));
        assert_eq!(parser.next_clause()?, Some(clause![-6]));
        assert_eq!(parser.next_clause()?, Some(clause![]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn eof_clause() -> Result<()> {
        let mut parser = Parser::from_read("1 2 -3 0\n4 5 0\n-6 0".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4, 5]));
        assert_eq!(parser.next_clause()?, Some(clause![-6]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn empty_lines() -> Result<()> {
        let mut parser = Parser::from_read("\n1 2 -3 0\n\n4 5 0\n\n-6 0\n\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4, 5]));
        assert_eq!(parser.next_clause()?, Some(clause![-6]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn split_clauses() -> Result<()> {
        let mut parser = Parser::from_read("1 2\n-3 0\n4 5\n0\n-6\n0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4, 5]));
        assert_eq!(parser.next_clause()?, Some(clause![-6]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn split_clauses_with_comments() -> Result<()> {
        let mut parser =
            Parser::from_read("1 2\nc 0\n-3 0\nc 0\n4 5\nc 0\n0\nc 0\n-6\nc 0\n0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4, 5]));
        assert_eq!(parser.next_clause()?, Some(clause![-6]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn empty_header() -> Result<()> {
        let mut parser = Parser::from_read("p cnf\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn empty_lines_before_header() -> Result<()> {
        let mut parser = Parser::from_read("\n\np cnf\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn var_only_header() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn full_header() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 1\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn early_comment() -> Result<()> {
        let mut parser = Parser::from_read("c 9 0\np cnf 3 1\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn mid_comment() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 1\nc 9 0\n1 2 -3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn late_comment() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 1\n1 2 -3 0\nc 9 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn crlf_newlines() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 1\r\n1 2 -3 0\r\nc 0\r\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn extra_misc_whitespace() -> Result<()> {
        let mut parser = Parser::from_read(" p\tcnf  3 1\t\n\t1\t 2\t-3\t0\r\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn leading_zeros_and_negative_zero() -> Result<()> {
        let mut parser = Parser::from_read(
            "p cnf 00000000000000000000004 002\n00001 02 -03 00\n 004 -00\n".as_bytes(),
        );

        assert_eq!(parser.next_clause()?, Some(clause![1, 2, -3]));
        assert_eq!(parser.next_clause()?, Some(clause![4]));
        assert_eq!(parser.next_clause()?, None);
        Ok(())
    }

    #[test]
    fn max_var_count() -> Result<()> {
        let input = format!("p cnf {}\n{0} -{0} 0\n", Var::MAX_VAR_COUNT);
        let mut parser = Parser::from_read(input.as_bytes());

        assert_eq!(
            parser.next_clause()?,
            Some(clause![Var::MAX_DIMACS, -Var::MAX_DIMACS])
        );
        Ok(())
    }

    #[test]
    fn err_exceeding_max_var_count() {
        let input = format!("p cnf {}\n", Var::MAX_VAR_COUNT + 1);
        let mut parser = Parser::from_read(input.as_bytes());

        assert!(matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        ));
    }

    #[test]
    fn err_negative_var_count() {
        let mut parser = Parser::from_read("p cnf -1".as_bytes());

        assert!(matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        ));
    }

    #[test]
    fn err_exceeding_max_clause_count() {
        let input = format!("p cnf 1 {}\n", (i64::MAX as u64) + 1);
        let mut parser = Parser::from_read(input.as_bytes());

        assert!(matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        ));
    }

    #[test]
    fn err_wrong_header() {
        let mut parser = Parser::from_read("p notcnf\n".as_bytes());

        assert!(matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        ));
    }

    #[test]
    fn err_wrong_header_line2() {
        let mut parser = Parser::from_read("\np\n".as_bytes());

        assert!(matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 2, .. })
        ));
    }

    #[test]
    fn err_missing_clauses() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 3, .. })
        );
        Ok(())
    }

    #[test]
    fn err_extra_clauses() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n2 0\n3 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_eq!(parser.next_clause()?, Some(clause![2]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 4, .. })
        );
        Ok(())
    }

    #[test]
    fn err_pos_lit_out_of_range() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n2 4 0".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 3, .. })
        );
        Ok(())
    }

    #[test]
    fn err_neg_lit_out_of_range() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n2 -4 0".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 3, .. })
        );
        Ok(())
    }

    #[test]
    fn err_unterminated_clause() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n2 -3".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 3, .. })
        );
        Ok(())
    }

    #[test]
    fn err_dangling_literal() -> Result<()> {
        let mut parser = Parser::from_read("p cnf 3 2\n1 -2 3 0\n2 -3 0 1 0\n".as_bytes());

        assert_eq!(parser.next_clause()?, Some(clause![1, -2, 3]));
        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 3, .. })
        );
        Ok(())
    }

    #[test]
    fn err_unexpected_token_var_count() {
        let mut parser = Parser::from_read("p cnf error 2\n".as_bytes());

        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        );
    }

    #[test]
    fn err_unexpected_token_clause_count() {
        let mut parser = Parser::from_read("p cnf 2 error\n".as_bytes());

        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        );
    }

    #[test]
    fn err_extra_header_field() {
        let mut parser = Parser::from_read("p cnf 2 1 2\n".as_bytes());

        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 1, .. })
        );
    }

    #[test]
    fn err_unexpected_token_clause() {
        let mut parser = Parser::from_read("p cnf 2 1\n 1 2 err 0\n".as_bytes());

        assert_matches!(
            parser.next_clause(),
            Err(ParseError::ParseError { line: 2, .. })
        );
    }
}
