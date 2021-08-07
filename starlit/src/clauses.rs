//! Storage for non-unit clauses including watch lists for efficient unit propagation.
use std::mem::take;

use long::{ClauseRef, LongClauses, SolverClauseData};

use crate::{lit::Lit, tracking::TracksVarCount, util::mut_scan::MutScan};

use self::long::ClauseRefGcMap;

pub mod long;

/// Storage for non-unit clauses including watch lists for efficient unit propagation.
#[derive(Default)]
pub struct Clauses {
    /// Binary clauses.
    pub binary: BinaryClauses,

    /// Long clauses.
    pub long: LongClauses,

    /// Watch lists for long clauses.
    pub watch_lists: WatchLists,
}

/// Reference to an added binary or long clause.
pub enum AddedClause {
    /// A reference to a binary clause, represented as the two contained literals.
    ///
    /// The order is the same as in the literals passed to [`Clauses::add_clause`].
    Binary([Lit; 2]),
    /// A reference to a long clause.
    Long(ClauseRef),
}

impl Clauses {
    /// Stores a new clause, returning a `ClauseRef` to the new clause if it is long.
    ///
    /// Returns a reference to the added clause.
    pub fn add_clause(&mut self, data: SolverClauseData, clause_lits: &[Lit]) -> AddedClause {
        match *clause_lits {
            [a, b] => {
                self.binary.add_clause([a, b]);
                AddedClause::Binary([a, b])
            }
            [a, b, ..] => {
                let clause = self.long.add_clause(data, clause_lits);
                self.watch_lists.watch_clause(clause, [a, b]);
                AddedClause::Long(clause)
            }
            _ => panic!(
                "cannot add unit or empty clause {:?} to Clauses",
                clause_lits
            ),
        }
    }
}

impl TracksVarCount for Clauses {
    fn var_count(&self) -> usize {
        self.binary.var_count()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.binary.set_var_count(var_count);
        self.watch_lists.set_var_count(var_count);
    }
}

/// Storage for binary clauses.
#[derive(Default)]
pub struct BinaryClauses {
    by_lit: Vec<Vec<Lit>>,
}

impl BinaryClauses {
    /// Stores a new binary clause.
    pub fn add_clause(&mut self, clause_lits: [Lit; 2]) {
        for i in 0..2 {
            let watched_lit = clause_lits[i];
            let implied_lit = clause_lits[i ^ 1];
            self.by_lit[watched_lit.code()].push(implied_lit);
        }
    }

    /// Returns all binary clauses containing the given literal.
    ///
    /// A clause is represented by a single literal; the other literal of the clause.
    pub fn containing(&self, lit: Lit) -> &[Lit] {
        &self.by_lit[lit.code()]
    }
}

impl TracksVarCount for BinaryClauses {
    fn var_count(&self) -> usize {
        self.by_lit.len() / 2
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.by_lit.resize(var_count * 2, vec![])
    }
}

/// Watchlist entry referencing a clause and a blocking literal.
pub struct Watch {
    /// The watched clause.
    pub clause: ClauseRef,
    /// A blocking literal of the watched clause.
    ///
    /// Used to quickly detect some satisfied long clauses during unit propagation. If this literal
    /// is already true, there is no need to read the watched clause from memory.
    ///
    /// This can be any literal of the watched clause apart from the literal to which the watch list
    /// containing this entry belongs.
    ///
    /// See also ["MiniSat 2.1 and MiniSat++ 1.0 — SAT Race 2008 Editions"][1].
    ///
    /// [1]:https://baldur.iti.kit.edu/sat-race-2008/descriptions/solver_26.pdf
    pub blocking_lit: Lit,
}

/// Watchlists for efficient unit propagation.
///
/// Every long clause has two watched literals. These literals are kept as first two literals in the
/// long clause storage. Additionally for each literal there is a watch list that has a reference to
/// every clause in which that literal is watched.
///
/// Whenever unit propagation finishes, it maintains the invariant that, unless a conflict was
/// detected, for each clause there either a) are two watched non-false literals, or b) there is a
/// true literal. All this in such a way that undoing assignments during backtracking will maintain
/// this invariant without moving any watches.
#[derive(Default)]
pub struct WatchLists {
    by_lit: Vec<Vec<Watch>>,
}

impl WatchLists {
    /// Adds watchlist entries for a new clause.
    ///
    /// Note that the watched literals should always be the first two literals of a clause.
    pub fn watch_clause(&mut self, clause: ClauseRef, watched_lits: [Lit; 2]) {
        for i in 0..2 {
            let watched_lit = watched_lits[i];
            let blocking_lit = watched_lits[i ^ 1];
            self.by_lit[watched_lit.code()].push(Watch {
                clause,
                blocking_lit,
            });
        }
    }

    /// Returns the watch list for clauses containing the given literal, replacing it with an empty
    /// list.
    pub fn take(&mut self, lit: Lit) -> Vec<Watch> {
        take(&mut self.by_lit[lit.code()])
    }

    /// Restores a watch list that was temporarily taken using [`take`](Self::take).
    pub fn restore(&mut self, lit: Lit, watches: Vec<Watch>) {
        debug_assert!(self.by_lit[lit.code()].is_empty());
        self.by_lit[lit.code()] = watches;
    }

    /// Appends a single `Watch` to the watch list for a given literal.
    pub fn push_watch(&mut self, lit: Lit, watch: Watch) {
        self.by_lit[lit.code()].push(watch);
    }

    /// Updates refrence to long clauses after garbage collection.
    pub fn update_clause_references(&mut self, gc_map: &ClauseRefGcMap) {
        for watches in &mut self.by_lit {
            let mut scan = MutScan::new(watches);
            while let Some(mut watch) = scan.next() {
                if let Some(clause) = gc_map.update(watch.clause) {
                    watch.clause = clause;
                    watch.keep();
                } else {
                    watch.remove();
                }
            }
        }
    }
}

impl TracksVarCount for WatchLists {
    fn var_count(&self) -> usize {
        self.by_lit.len() / 2
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.by_lit.resize_with(var_count * 2, Default::default)
    }
}
