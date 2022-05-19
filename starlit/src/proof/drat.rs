//! Writer for the DRAT clausal proof file format.
use super::Proof;

/// Writer for the text based DRAT clausal proof file format.
pub struct Drat<'a> {
    target: flussab::DeferredWriter<'a>,
}

impl<'a> Drat<'a> {
    /// Creates a new writer writing into a given [`flussab::DeferredWriter`].
    pub fn new(target: flussab::DeferredWriter<'a>) -> Self {
        Self { target }
    }
}

impl Proof for Drat<'_> {
    fn add_clause(&mut self, lits: &[crate::lit::Lit]) {
        for &lit in lits {
            flussab::write::text::ascii_digits(&mut self.target, lit.dimacs());
            self.target.write_all_defer_err(b" ");
        }
        self.target.write_all_defer_err(b"0\n");
    }

    fn delete_clause(&mut self, lits: &[crate::lit::Lit]) {
        self.target.write_all_defer_err(b"d ");
        self.add_clause(lits);
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.target.flush_defer_err();
        self.target.check_io_error()
    }
}

/// Writer for the binary DRAT clausal proof file format.
pub struct BinaryDrat<'a> {
    target: flussab::DeferredWriter<'a>,
}

impl<'a> BinaryDrat<'a> {
    /// Creates a new writer writing into a given [`flussab::DeferredWriter`].
    pub fn new(target: flussab::DeferredWriter<'a>) -> Self {
        Self { target }
    }

    fn write_lits(&mut self, lits: &[crate::lit::Lit]) {
        for &lit in lits {
            self.write_lit(lit);
        }
        self.target.write_all_defer_err(&[0]);
    }

    fn write_lit(&mut self, lit: crate::lit::Lit) {
        // TODO add more efficient variable length integer encoders/decoders to flussab and use them
        // here
        let mut drat_code = (!lit).code() + 2;
        while drat_code >= 0x80 {
            self.target.write_all_defer_err(&[(drat_code as u8) | 0x80]);
            drat_code >>= 7;
        }
        self.target.write_all_defer_err(&[drat_code as u8]);
    }
}

impl Proof for BinaryDrat<'_> {
    fn add_clause(&mut self, lits: &[crate::lit::Lit]) {
        self.target.write_all_defer_err(b"a");
        self.write_lits(lits);
    }

    fn delete_clause(&mut self, lits: &[crate::lit::Lit]) {
        self.target.write_all_defer_err(b"d");
        self.write_lits(lits);
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.target.flush_defer_err();
        self.target.check_io_error()
    }
}
