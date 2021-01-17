//! Parsing of DIMACS style file formats.
//!
//! This includes DIMACS CNF files, extensions of that format as well as many other formats using
//! similar conventions.
use std::{
    fmt::Display,
    io::{self, BufReader, Cursor, Read},
};

use bstr::BStr;
use static_assertions::const_assert;

pub mod cnf;

/// A token of a DIMACS style file format.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Token<'a> {
    /// The kind of token this represents.
    pub kind: TokenKind,
    /// Bytes of the token.
    pub bytes: &'a BStr,
    /// Value of an `Int` token, otherwise unspecified.
    pub value: i64,
    /// Line of the bytes following this token
    pub line: usize,
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            TokenKind::Comment => f.write_str("comment"),
            TokenKind::Newline => f.write_str("end of line"),
            TokenKind::Int => write!(f, "{}", self.bytes),
            TokenKind::BigInt => write!(f, "{}", self.bytes),
            TokenKind::Word => write!(f, "{:?}", self.bytes),
            TokenKind::EndOfFile => f.write_str("end of file"),
            TokenKind::IoError => f.write_str("io error"),
        }
    }
}

impl<'a> Token<'a> {
    pub fn is_negative(&self) -> bool {
        match self.kind {
            TokenKind::Int => self.value < 0,
            TokenKind::BigInt => self.bytes[0] == b'-',
            _ => false,
        }
    }
}

// Changing the numeric values of the tokens requries adjusting code that uses them!

/// Kinds of token in a DIMACS style file format.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[repr(u8)]
pub enum TokenKind {
    /// A whole line starting with `'c'` including the final newline.
    Comment = 0,
    /// A newline character.
    ///
    /// Not emitted for comment lines
    Newline = 1,
    /// An integer that can be represented as an `i64`.
    Int = 2,
    /// An integer outside of the `i64` range.
    BigInt = 3,
    /// Any other sequence of non-whitespace characters.
    ///
    /// The characters `' '`, `'\t'`, `'\r'` and '`\n`' count as whitespace.
    Word = 4,
    /// Token indicating the end of file was reached without encountering IO errors.
    EndOfFile = 5,
    /// Token indicating an IO error occured.
    ///
    /// The error can be accessed using [`Tokenizer::check_io_error`].
    IoError = 6,
}

impl TokenKind {
    #[inline(always)]
    pub fn terminates_line(self) -> bool {
        self as u8 <= TokenKind::Newline as u8
    }

    #[inline(always)]
    pub fn last(self) -> bool {
        self as u8 >= TokenKind::EndOfFile as u8
    }
}

/// Internal compact and reference free representation of tokens.
struct TokenData {
    /// The kind of token this represents.
    kind: TokenKind,
    /// Offset within the tokenizers buffer.
    ///
    /// Ignored for overlong tokens
    begin: u16,
    /// Length of the token.
    ///
    /// For overlong tokens that do not fit in the fixed buffer, this is set to `0`, indicating that
    /// the tokenizer's `overlong_buf` contains the token.
    len: u16,
    /// Value of an `Int` token, otherwise unspecified.
    value: i64,
}

/// Buffer size for tokenizing.
///
/// Input is read one buffer at a time and the tokenizer scans the complete buffer. Partial tokens
/// at the end of the buffer are kept and rescanned after refilling the buffer. Tokens longer than
/// the buffer are handled separately.
const BUF_SIZE: usize = 4 << 10;

/// Extra padding at the end of the buffer to avoid range checks while scanning.
const BUF_PADDING_END: usize = 1;

/// Allocation size for the tokenizing buffer.
const BUF_ALLOC_SIZE: usize = BUF_SIZE + BUF_PADDING_END;

// We use `u16` values to represent offsets and lengths within the tokenizing buffer.
const_assert!(BUF_SIZE <= u16::MAX as usize);

/// Scan and tokenize a file in a DIMACS style format.
pub struct Tokenizer<'a> {
    /// Source of input data.
    read: Box<dyn Read + 'a>,
    /// Tokenizing buffer.
    buf: Box<[u8; BUF_ALLOC_SIZE]>,
    /// Amount of valid data in buf.
    len: usize,
    /// Offset where scanning should continue.
    scanned_upto: usize,
    /// Buffered tokens.
    tokens: Vec<TokenData>,
    /// Index of current token.
    current_token_index: usize,
    /// Did we encounter EOF of `read`?
    eof_reached: bool,
    /// First token on a line?
    at_begin_of_line: bool,
    /// Did an IO error occur?
    io_error: Option<io::Error>,
    /// Buffer for scanning overlong tokens.
    overlong_buf: Vec<u8>,
    /// The lind of the token after the current token.
    line: usize,
    /// Set by `advance` unset by `current_token`.
    advanced: bool,
}

impl<'a> Tokenizer<'a> {
    /// Initialize a [`Tokenizer`] from a [`BufReader`].
    pub fn from_buf_reader(buf_reader: BufReader<impl Read + 'a>) -> Self {
        // Avoid double buffering without discarding any already buffered contents.
        let buf_data = buf_reader.buffer().to_vec();
        if buf_data.is_empty() {
            Self::from_read(buf_reader.into_inner())
        } else {
            Self::from_read(Cursor::new(buf_data).chain(buf_reader.into_inner()))
        }
    }

    /// Initialize a [`Tokenizer`] with an underlying [`Read`] instance.
    ///
    /// If the [`Read`] instance is a [`BufReader`], it is better to use
    /// [`from_buf_reader`][Self::from_buf_reader] to avoid unnecessary copying of the read data.
    pub fn from_read(read: impl Read + 'a) -> Self {
        Self::from_boxed_dyn_read(Box::new(read))
    }

    /// Initialize a [`Tokenizer`] with an underlying boxed [`Read`] instance.
    ///
    /// If the [`Read`] instance is a [`BufReader`], it is better to use
    /// [`from_buf_reader`][Self::from_buf_reader] to avoid unnecessary copying of the read data.
    #[inline(never)]
    pub fn from_boxed_dyn_read(read: Box<dyn Read + 'a>) -> Self {
        Tokenizer {
            read,
            buf: Box::new([0; BUF_ALLOC_SIZE]),
            len: 0,
            scanned_upto: 0,
            tokens: vec![],
            current_token_index: 0,
            eof_reached: false,
            at_begin_of_line: true,
            io_error: None,
            overlong_buf: vec![],
            line: 1,
            advanced: true,
        }
    }

    /// Get current token, processing more input when required.
    ///
    /// Any IO errors that occur while processing more input result in a [`TokenKind::IoError`]
    /// token. The corresponding error value can be accessed via
    /// [`check_io_error`][Self::check_io_error].
    #[inline]
    pub fn current_token(&mut self) -> Token {
        if let Some(&TokenData {
            kind,
            begin,
            len,
            value,
        }) = self.tokens.get(self.current_token_index)
        {
            self.line += (kind.terminates_line() & self.advanced) as usize;
            self.advanced = false;
            Token {
                kind,
                bytes: if len == 0 {
                    self.overlong_buf.as_slice().into()
                } else {
                    self.buf[begin as usize..][..len as usize].into()
                },
                value,
                line: self.line - kind.terminates_line() as usize,
            }
        } else {
            self.current_token_slowpath()
        }
    }

    #[inline(always)]
    /// Advance to the next token.
    ///
    /// This may be called even after reaching `TokenKind::EndOfFile` or `TokenKind::IoError`, in
    /// which case this is a no-op.
    pub fn advance(&mut self) {
        self.current_token_index += 1;
        self.advanced = true;
    }

    /// Return any encountered IO errors.
    pub fn check_io_error(&mut self) -> io::Result<()> {
        if let Some(err) = self.io_error.take() {
            Err(err)
        } else {
            Ok(())
        }
    }

    /// The line number of the current token.
    ///
    /// The first line is line number 1.
    pub fn current_line(&mut self) -> usize {
        self.line - (!self.advanced & self.current_token().kind.terminates_line()) as usize
    }

    #[cold]
    #[inline(never)]
    /// Refill the internal buffer, scan for tokens and fall back to overlong token handling if
    /// necessary.
    fn current_token_slowpath(&mut self) -> Token {
        // This should only be called when the buffered tokens are exhausted
        assert!(self.current_token_index >= self.tokens.len());

        if self.eof_reached {
            // When we reached EOF or encountered an error we'll always buffer a single
            // corresponding token and return.
            self.tokens.clear();
            self.current_token_index = 0;
            self.overlong_buf.clear();
            self.tokens.push(TokenData {
                kind: if self.io_error.is_some() {
                    TokenKind::IoError
                } else {
                    TokenKind::EndOfFile
                },
                begin: 0,
                len: 0,
                value: 0,
            });
            return self.current_token();
        }

        // Otherwise we reset the buffered token, and shift the pending input data to the beginning
        // of th buffer
        self.tokens.clear();
        self.current_token_index = 0;
        self.buf.copy_within(self.scanned_upto..self.len, 0);
        self.len -= self.scanned_upto;
        self.scanned_upto = 0;

        // As long as we didn't produce any tokens, haven't reached the end of file and have space
        // left in the buffer, we read and scan more input data
        while self.tokens.is_empty() && self.len < BUF_SIZE && !self.eof_reached {
            match self.read.read(&mut self.buf[self.len..BUF_SIZE]) {
                Ok(0) => self.eof_reached = true,
                Ok(n) => self.len += n,
                Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                Err(err) => {
                    self.io_error = Some(err);
                    self.eof_reached = true
                }
            }

            // Scan the newly read data for tokens
            self.scan();

            // If this hasn't produced any tokens, but we did scan over half of the buffer, shift
            // the remaining data in the buffer back to the beginning.
            if self.tokens.is_empty() && self.scanned_upto >= BUF_SIZE / 2 {
                // This ensures that we only enter overlong tokens mode if a token is longer than
                // `BUF_SIZE / 2`. This also makes sure that we only enter overlong mode at the
                // start of a token, as each call to `scan` will skip any whitespace.
                self.buf.copy_within(self.scanned_upto..self.len, 0);
                self.len -= self.scanned_upto;
                self.scanned_upto = 0;
            }
        }

        // If we produced no tokens but haven't reached EOF, this means that there is an
        // unterminated token that reaches the end of the buffer, i.e. and overlong token. This is
        // processed using a separate slower routine that uses a dynamically resized buffer.
        if self.tokens.is_empty() && !self.eof_reached {
            self.scan_overlong();
        }

        // At this point we have at least one buffered token so we can return it
        self.current_token()
    }

    /// Parses a single whitespace delimited token.
    fn parse_token(token_bytes: &[u8]) -> (TokenKind, i64) {
        let digits = &token_bytes[(token_bytes[0] == b'-') as usize..];

        if !digits.is_empty() && digits.iter().all(|digit| matches!(digit, b'0'..=b'9')) {
            // SAFETY we checked that `token_bytes` only consists of digits and the
            // minus sign, so as pure ASCII it is also valid UTF-8.
            let token_str = unsafe { std::str::from_utf8_unchecked(token_bytes) };
            if let Ok(value) = str::parse::<i64>(token_str) {
                (TokenKind::Int, value)
            } else {
                (TokenKind::BigInt, 0)
            }
        } else {
            (TokenKind::Word, 0)
        }
    }

    /// Handle an overlong token that does not fit into the fixed buffer.
    ///
    /// This assumes `scanned_upto` is at the start of the overlong token already and that the token
    /// continuous until `len` i.e. the end of the valid data in the buffer.
    #[inline(never)]
    fn scan_overlong(&mut self) {
        let mut len = self.len - self.scanned_upto;
        let mut pos = len;
        self.overlong_buf.clear();
        self.overlong_buf
            .extend_from_slice(&self.buf[self.scanned_upto..self.len]);

        loop {
            self.overlong_buf
                .resize(len + BUF_SIZE + BUF_PADDING_END, 0);

            loop {
                match self.read.read(&mut self.overlong_buf[len..len + BUF_SIZE]) {
                    Ok(0) => self.eof_reached = true,
                    Ok(n) => len += n,
                    Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                    Err(err) => {
                        self.io_error = Some(err);
                        self.eof_reached = true
                    }
                }
                break;
            }

            self.overlong_buf[len] = 0;

            if self.overlong_buf[0] == b'c' && self.at_begin_of_line {
                // Overlong token is a comment, scan until newline (inclusive) or EOF
                while match self.overlong_buf[pos] {
                    b'\n' => false,
                    0 if pos == len => false,
                    _ => true,
                } {
                    pos += 1;
                }
                if self.overlong_buf[pos] == 0 {
                    // Reached end of overlong buffer, read more data of not at EOF
                    if !self.eof_reached {
                        continue;
                    }
                } else {
                    pos += 1;
                }

                // Move remaining data after the token into the fixed buffer
                self.buf[..len - pos].copy_from_slice(&self.overlong_buf[pos..len]);
                self.overlong_buf.truncate(pos);
                self.scanned_upto = 0;
                self.len = len - pos;

                self.tokens.push(TokenData {
                    kind: TokenKind::Comment,
                    begin: 0,
                    len: 0,
                    value: 0,
                });

                // Process remaining data now in fixed buffer
                self.scan();

                return;
            } else {
                // Normal token, scan until whitespace, then classify
                assert!(!matches!(
                    self.overlong_buf[0],
                    b' ' | b'\t' | b'\r' | b'\n'
                ));

                while match self.overlong_buf[pos] {
                    b'\n' | b' ' | b'\t' | b'\r' => false,
                    0 if pos == len => false,
                    _ => true,
                } {
                    pos += 1;
                }

                if self.overlong_buf[pos] == 0 && !self.eof_reached {
                    // Reached end of overlong buffer and not at EOF, read more data
                    continue;
                }

                // Move remaining data after the token into the fixed buffer
                self.buf[..len - pos].copy_from_slice(&self.overlong_buf[pos..len]);
                self.overlong_buf.truncate(pos);
                self.scanned_upto = 0;
                self.len = len - pos;
                self.at_begin_of_line = false;

                let (kind, value) = Self::parse_token(&self.overlong_buf);

                self.tokens.push(TokenData {
                    kind,
                    begin: 0,
                    len: 0,
                    value,
                });

                // Process remaining data now in fixed buffer
                self.scan();
                return;
            }
        }
    }

    /// Process data `scanned_upto..len` in the fixed buffer
    #[inline(never)]
    fn scan(&mut self) {
        // Add sentinel byte for efficient end of buffer checks
        self.buf[self.len] = 0;
        loop {
            let first_byte = self.buf[self.scanned_upto];
            match first_byte {
                // If we reach a 0 byte, check whether we are at the end
                0 if self.scanned_upto == self.len => break,
                // If we have a 'c' byte as first character, this starts a comment
                b'c' if self.at_begin_of_line => {
                    // Scan until we find a newline or the end of the buffer
                    let mut pos = self.scanned_upto;
                    while match self.buf[pos] {
                        b'\n' => false,
                        0 if pos == self.len => false,
                        _ => true,
                    } {
                        pos += 1;
                    }

                    if self.buf[pos] == 0 {
                        // If we are not at EOF the comment continues past the current buffer so
                        // don't emit a token yet
                        if !self.eof_reached {
                            break;
                        }
                    } else {
                        pos += 1;
                    }
                    let begin = self.scanned_upto as u16;
                    let len = (pos - self.scanned_upto) as u16;
                    self.scanned_upto = pos;

                    self.tokens.push(TokenData {
                        kind: TokenKind::Comment,
                        begin,
                        len,
                        value: 0,
                    });
                }
                b' ' | b'\t' | b'\r' => {
                    // Skip any non-linebreak whitespace
                    self.scanned_upto += 1;
                    self.at_begin_of_line = false;
                }
                b'\n' => {
                    // Emit a newline token
                    self.tokens.push(TokenData {
                        kind: TokenKind::Newline,
                        begin: self.scanned_upto as u16,
                        len: 1,
                        value: 0,
                    });
                    self.scanned_upto += 1;
                    self.at_begin_of_line = true;
                }
                _ => {
                    // Any other token is delimited by whitespace
                    let mut pos = self.scanned_upto;
                    while match self.buf[pos] {
                        b'\n' | b' ' | b'\t' | b'\r' => false,
                        0 if pos == self.len => false,
                        _ => true,
                    } {
                        pos += 1;
                    }

                    if self.buf[pos] == 0 && !self.eof_reached {
                        // If we reached the end of the buffer before finding whitespace, the token
                        // continues so don't emit anything yet
                        break;
                    }

                    let (kind, value) = Self::parse_token(&self.buf[self.scanned_upto..pos]);

                    let begin = self.scanned_upto as u16;
                    let len = (pos - self.scanned_upto) as u16;
                    self.scanned_upto = pos;

                    self.tokens.push(TokenData {
                        kind,
                        begin,
                        len,
                        value,
                    });
                    self.at_begin_of_line = false;
                }
            }
        }
    }
}
