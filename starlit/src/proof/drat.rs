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
