//! Storage for binary clauses.
use crate::{lit::Lit, tracking::Resize, util::vec_map::VecMap};

/// Storage for binary clauses.
#[derive(Default)]
pub struct BinaryClauses {
    by_lit: VecMap<Lit, Vec<Lit>>,
}

impl BinaryClauses {
    /// Stores a new binary clause.
    pub fn add_clause(&mut self, clause_lits: [Lit; 2]) {
        for i in 0..2 {
            let watched_lit = clause_lits[i];
            let implied_lit = clause_lits[i ^ 1];
            self.by_lit[watched_lit].push(implied_lit);
        }
    }

    /// Returns all binary clauses containing the given literal.
    ///
    /// A clause is represented by a single literal; the other literal of the clause.
    pub fn containing(&self, lit: Lit) -> &[Lit] {
        &self.by_lit[lit]
    }
}

impl Resize for BinaryClauses {
    fn resize(&mut self, var_count: usize) {
        self.by_lit.resize(var_count * 2, vec![])
    }
}
