//! Clause database reduction.

use crate::{search::Search, trail::Reason};

/// References to all data used during clause database reduction.
#[allow(missing_docs)]
pub struct ReduceOps<'a> {
    pub search: &'a mut Search,
}

impl<'a> ReduceOps<'a> {
    /// Performs clause database reduction.
    pub fn reduce(&mut self) {
        tracing::debug!("reduce");
        self.protect_clauses(true);

        let long_clauses = &mut self.search.clauses.long;
        let mut clause_iter = None;
        while let Some(clause) = long_clauses.next_clause(&mut clause_iter) {
            let data = long_clauses.data(clause);
            if data.protected() {
                continue;
            }
            if !data.redundant() {
                continue;
            }
            if data.glue() <= 2 {
                continue;
            }
            long_clauses.delete_clause(clause);
        }
        self.protect_clauses(false);
    }

    /// Sets or resets the protected bit for all currently propagating long clauses.
    fn protect_clauses(&mut self, protected: bool) {
        for step in self.search.trail.steps() {
            if let Reason::Long(clause) = step.reason {
                self.search
                    .clauses
                    .long
                    .data_mut(clause)
                    .set_protected(protected);
            }
        }
    }
}
