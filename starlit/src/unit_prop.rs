//! Unit propagation for CNF clauses.
//!
//! This implements watch list based unit propagation for CNF clauses. Unit propagation is the
//! process of repeatedly extending the current partial assignment by all literals propagated by
//! clauses that are unit under the current assignment until none are left or until a clause is in
//! conflict.
use crate::{
    clauses::Clauses,
    conflict_analysis::ConflictClause,
    lit::Lit,
    trail::{BacktrackCallbacks, Reason, Step, Trail},
    util::mut_scan::MutScan,
};

/// Tracks the state of unit propagation
#[derive(Default)]
pub struct UnitProp {
    /// Size of the trail's prefix for which unit propagation was performed.
    pub propagated: usize,
}

impl BacktrackCallbacks for UnitProp {
    fn backtracked(&mut self, trail: &Trail) {
        self.propagated = self.propagated.min(trail.steps().len());
    }
}

/// References to all data used during unit propagation.
#[allow(missing_docs)]
pub struct UnitPropOps<'a> {
    pub trail: &'a mut Trail,
    pub clauses: &'a mut Clauses,
    pub unit_prop: &'a mut UnitProp,
}

impl<'a> UnitPropOps<'a> {
    /// Performs unit propagation.
    pub fn propagate(&mut self) -> Result<(), ConflictClause> {
        while self.unit_prop.propagated < self.trail.steps().len() {
            self.propagate_literal(self.trail.steps()[self.unit_prop.propagated].assigned_lit)?;
            self.unit_prop.propagated += 1;
        }
        Ok(())
    }

    /// Finds clauses that become unit or falsified when `lit` is assigned true.
    fn propagate_literal(&mut self, lit: Lit) -> Result<(), ConflictClause> {
        self.propagate_binary_clauses(lit)?;
        self.propagate_long_clauses(lit)?;
        Ok(())
    }

    /// Finds binary clauses that become unit or falsified when `lit` is assigned true.
    fn propagate_binary_clauses(&mut self, lit: Lit) -> Result<(), ConflictClause> {
        // `lit` is assigned `true`, so clauses containing `!lit` could become unit or falsified.
        let clause_lit = !lit;

        for &other_lit in self.clauses.binary.containing(clause_lit) {
            // If the clause is already satisfied, there is nothing to do
            if !self.trail.assigned.is_true(other_lit) {
                // If the other literal is also false, the clause is in conflict
                if self.trail.assigned.is_false(other_lit) {
                    return Err(ConflictClause::Binary([clause_lit, other_lit]));
                } else {
                    // Otherwise the clause is unit and non-satisfied, so we propagate its other
                    // literal
                    self.trail.assign(Step {
                        assigned_lit: other_lit,
                        decision_level: self.trail.decision_level(),
                        reason: Reason::Binary(clause_lit),
                    })
                }
            }
        }

        Ok(())
    }

    /// Finds long clauses that become unit or falsified when `lit` is assigned true.
    fn propagate_long_clauses(&mut self, lit: Lit) -> Result<(), ConflictClause> {
        // `lit` is assigned `true`, so clauses containing `!lit` could become unit or falsified.
        let watched_lit = !lit;

        let mut watches = self.clauses.watch_lists.take(watched_lit);

        let mut scan = MutScan::new(&mut watches);

        let mut result = Ok(());

        'outer: while let Some(mut watch) = scan.next() {
            // We need to maintain the invariant that, unless we detected a conflict, for each
            // clause there either a) are two watched non-false literals, or b) there is a true
            // literal. All this in such a way that undoing assignments during backtracking will
            // maintain this invariant without moving any watches.
            //
            // If the blocked literal or the other watched literal are true, b) holds and we are
            // done.
            //
            // Otherwise we search for a non-false literal among the non-watched literals.
            //
            // If we find an unassigned literal we move our watch to it. For the case where the
            // other watched literal is non-false, this restores a). If the other watched literal is
            // false, this is not yet the case, but this means that the other watched literal is
            // still pending on the propagation queue and we will restore the invariant when we get
            // around to process it. Thus, in both cases we are done.
            //
            // If we find a true literal b) also holds, so we would not have to do anything. If we
            // don't do anything at all, though, the next time the watched literal gets re-assigned
            // the same value, we would again search the non-watched literals. We can avoid this in
            // two ways: 1) we set the blocking literal of our watch to the found literal or 2) we
            // move the watch to the found literal, the same way as we do when we find an unassigned
            // literal.
            //
            // As 1) only touches memory that we already accessed, this is what we use.
            //
            // Finally, if there is no other non-false literal, all but the other watched literal
            // must be false. If the other watched literal is also false, we have a conflict.
            // Otherwise this clause asserts the other watched literal, enqueuing a new propagation
            // and turning it from unassigned to true. After that b) holds again.

            if self.trail.assigned.is_true(watch.blocking_lit) {
                watch.keep();
                continue; // Clause already satisfied by `blocking_lit`.
            }
            let (clause_data, clause_lits) = self.clauses.long.data_and_lits_mut(watch.clause);
            if clause_lits.len() < 2 {
                // This only happens when the clause was deleted but not yet collected.
                watch.remove(); // No need to continue watching a deleted clause.
                continue;
            }

            // The two watched literals are always kept in the first two slots
            let other_watched_lit = watched_lit.select_other(clause_lits[0], clause_lits[1]);

            if self.trail.assigned.is_true(other_watched_lit) {
                // Clause is already satisfied by the other watched literal, so we replace the
                // blocking literal to increase the chance of detecting this early the next time we
                // scan this watch list.
                watch.blocking_lit = other_watched_lit;

                watch.keep();
                continue;
            }

            // When searching for a non-false non-watched literal, we continue where the last such
            // search for this clause stopped. This avoids accidentally quadratic behaviour, in case
            // a large prefix of the clause is falsified early on the trail.
            //
            // See also ["Optimal Implementation of Watched Literals and More General
            // Techniques"](https://doi.org/10.1613/jair.4016)
            let mut search_pos = clause_data.search_pos();

            let search_len = clause_lits.len() - 2;

            for _ in 0..search_len {
                let search_lit = clause_lits[2 + search_pos];
                if !self.trail.assigned.is_false(search_lit) {
                    // We found a non-false literal!
                    if self.trail.assigned.is_true(search_lit) {
                        // It is true, no need to move the watch, but update the blocking literal
                        watch.blocking_lit = search_lit;
                        clause_data.set_search_pos(search_pos);

                        watch.keep();
                    } else {
                        // It is unassigned, move our watch
                        watch.blocking_lit = other_watched_lit;
                        self.clauses
                            .watch_lists
                            .push_watch(search_lit, watch.remove());
                        clause_data.set_search_pos(search_pos);
                        // Move the newly watched literal to the beginning of the clause
                        clause_lits[0] = search_lit; // Newly watched
                        clause_lits[1] = other_watched_lit;
                        clause_lits[2 + search_pos] = watched_lit; // Not watched anymore
                    }
                    continue 'outer;
                }
                search_pos += 1;
                if search_pos == search_len {
                    // TODO make this branchfree? benchmark!
                    search_pos = 0;
                }
            }
            clause_data.set_search_pos(search_pos);

            // All non-watched literals, as well as `watched_lit` are false

            if self.trail.assigned.is_false(other_watched_lit) {
                // All literals are false, i.e. we have a conflict
                result = Err(ConflictClause::Long(watch.clause));

                watch.keep();
                break;
            } else {
                // This clause asserts `other_watched_lit`.

                // Make sure the asserted literal is the first, so the asserting literals form a
                // contiguous slice.
                clause_lits[0] = other_watched_lit;
                clause_lits[1] = watched_lit;

                self.trail.assign(Step {
                    assigned_lit: other_watched_lit,
                    decision_level: self.trail.decision_level(),
                    reason: Reason::Long(watch.clause),
                });

                watch.keep();
            }
        }

        drop(scan);

        self.clauses.watch_lists.restore(!lit, watches);

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{clauses::long::SolverClauseData, tracking::TracksVarCount};

    use super::*;

    macro_rules! clause {
        ($($lit:literal),* $(,)?) => {{
            [$(Lit::from_dimacs($lit)),*]
        }};
    }

    macro_rules! clauses {
        ($var_count:literal vars $($($lit:literal),+);* $(;)?) => {{
            let mut clauses = Clauses::default();
            clauses.set_var_count($var_count);
            $(
                clauses.add_clause(SolverClauseData::default(), &[$(Lit::from_dimacs($lit)),*]);
            )*
            clauses
        }};
    }

    macro_rules! unit_prop {
        ($unit_prop:ident, $clauses:ident) => {
            let mut trail = Trail::default();
            trail.set_var_count($clauses.var_count());
            let mut unit_prop = UnitProp::default();
            let mut $unit_prop = UnitPropOps {
                trail: &mut trail,
                clauses: &mut $clauses,
                unit_prop: &mut unit_prop,
            };
        };
    }

    macro_rules! assert_assigned {
        ($unit_prop:ident, $($lit:literal),*) => {
            let mut assigned = $unit_prop
                .trail
                .steps()
                .iter()
                .map(|step| step.assigned_lit)
                .collect::<Vec<_>>();
            let mut expected = vec![$(Lit::from_dimacs($lit)),*];
            assigned.sort_unstable();
            expected.sort_unstable();
            assert_eq!(assigned, expected);
        };
    }

    #[test]
    fn simple_prop() {
        let mut clauses = clauses![4 vars
            -1, 2;
            -2, 3;
            -2, -3, -4;
        ];
        unit_prop![unit_prop, clauses];

        unit_prop.trail.assign_decision(Lit::from_dimacs(1));
        assert!(unit_prop.propagate().is_ok());
        assert_assigned!(unit_prop, 1, 2, 3, -4);
    }

    #[test]
    fn two_step_prop() {
        let mut clauses = clauses![7 vars
            -1, 2;
            -2, 3;
            -2, -3, -4, -5, -6, -7;
            -4, 5;
            -5, 6;
        ];
        unit_prop![unit_prop, clauses];

        unit_prop.trail.assign_decision(Lit::from_dimacs(1));
        assert!(unit_prop.propagate().is_ok());
        assert_assigned!(unit_prop, 1, 2, 3);

        unit_prop.trail.assign_decision(Lit::from_dimacs(4));
        assert!(unit_prop.propagate().is_ok());
        assert_assigned!(unit_prop, 1, 2, 3, 4, 5, 6, -7);
    }

    #[test]
    fn binary_conflict() {
        let mut clauses = clauses![3 vars
            -1, 2;
            -1, 3;
            -2, -3;
        ];
        unit_prop![unit_prop, clauses];

        unit_prop.trail.assign_decision(Lit::from_dimacs(1));
        match unit_prop.propagate() {
            Err(ConflictClause::Binary(mut binary)) => {
                binary.sort();
                assert_eq!(binary, clause![-2, -3]);
            }
            _ => panic!("expected binary conflict"),
        }
    }

    #[test]
    fn long_conflict() {
        let mut clauses = clauses![8 vars
            -1, 2;
            -1, 3;
            -2, -3, 4;
            -3, 5;
            -4, -2, -3, -5, -1, -7, -8;
            -6, 7;
            -6, 8;
        ];
        unit_prop![unit_prop, clauses];

        unit_prop.trail.assign_decision(Lit::from_dimacs(1));
        assert!(unit_prop.propagate().is_ok());

        unit_prop.trail.assign_decision(Lit::from_dimacs(6));
        match unit_prop.propagate() {
            Err(ConflictClause::Long(clause)) => {
                let mut conflict_lits = clauses.long.lits(clause).to_vec();
                conflict_lits.sort();
                assert_eq!(conflict_lits, clause![-1, -2, -3, -4, -5, -7, -8]);
            }
            _ => panic!("expected long conflict"),
        }
    }
}
