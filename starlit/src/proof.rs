//! Proof logging
use crate::lit::Lit;

pub mod drat;

/// Trait implemented by proof format writers.
///
/// Currently only supports DRAT but will be extended to handle more formats.
pub trait Proof {
    /// Logs the addition of a clause.
    fn add_clause(&mut self, lits: &[Lit]);

    /// Logs the removal of a clause.
    fn delete_clause(&mut self, lits: &[Lit]);

    /// Flushes any buffered proof steps and reports any deferred IO errors.
    fn flush(&mut self) -> std::io::Result<()>;
}
