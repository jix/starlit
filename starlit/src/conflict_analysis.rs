//! Conflict analysis.
use std::mem::replace;

use crate::{
    clauses::{long::ClauseRef, Clauses},
    lit::Lit,
    trail::{Reason, Step, Trail},
};

/// Reference to a falsified clause.
#[derive(Debug)]
pub enum ConflictClause {
    /// The falsified clause is a binary clause.
    Binary([Lit; 2]),
    /// The falsified clause is a long clause.
    Long(ClauseRef),
}

impl ConflictClause {
    /// Returns the literals of the conflict clause.
    pub fn lits<'a>(&'a self, clauses: &'a Clauses) -> &'a [Lit] {
        match self {
            ConflictClause::Binary(lits) => &lits[..],
            ConflictClause::Long(clause) => clauses.long.lits(*clause),
        }
    }
}

/// Data used exclusively during conflict analysis.
#[derive(Default)]
pub struct ConflictAnalysisData {
    /// Literals of the current conflicting clause.
    ///
    /// Every true value corresponds to the literal assigned in the trail step of the same index.
    ///
    /// This is initialized to the literals of the conflict clause and is modified by successively
    /// resolving it with the reason for falsifying a contained literal until an asserting 1-UIP
    /// clause is found.
    current_clause_lits: Vec<bool>,

    /// Literals of the final derived asserting clause.
    ///
    /// Before a 1-UIP clause is found, this only contains literals below the current decision
    /// level.
    derived_clause: Vec<Lit>,

    /// Number of literals of the current decision level in the current conflicting clause.
    current_level_lit_count: usize,
}

impl ConflictAnalysisData {
    /// Reserves enough buffer space for analyzing the current conflict.
    fn update_trail_len(&mut self, trail_len: usize) {
        self.current_clause_lits
            .resize(self.current_clause_lits.len().max(trail_len), false);
    }
}

/// References to all data used during conflict analysis.
pub struct ConflictAnalysis<'a> {
    /// Trail and resulting partial assignment.
    pub trail: &'a mut Trail,
    /// The formula where propagation caused a conflict.
    pub clauses: &'a mut Clauses,
    /// Conflict analysis exclusive data.
    pub data: &'a mut ConflictAnalysisData,
}

impl<'a> ConflictAnalysis<'a> {
    /// Analyzes a conflict, learning a new clause that avoids that conflict in the future.
    ///
    /// This derives an asserting 1-UIP clause and backtracks such that the new clause is no longer
    /// in conflict, but instead propagates a new assignment.
    ///
    /// This only propagates a single new literal and needs to be followed by unit propagation.
    pub fn analyze_conflict(&mut self, conflict: ConflictClause) {
        assert!(self.trail.decision_level() != 0);
        self.derive_1uip_clause(conflict);
        self.backtrack();
        self.learn_and_propagate();
    }

    /// Adds the derived clause to the current formula and propagate the newly asserted literal.
    fn learn_and_propagate(&mut self) {
        let reason: Reason = if self.data.derived_clause.len() == 1 {
            Reason::Unit
        } else {
            self.clauses.add_clause(&self.data.derived_clause).into()
        };

        #[cfg(debug_assertions)]
        for &lit in &self.data.derived_clause[1..] {
            debug_assert!(self.trail.assigned.is_false(lit));
        }

        self.trail.assign(Step {
            assigned_lit: self.data.derived_clause[0],
            decision_level: self.trail.decision_level(),
            reason,
        });
    }

    /// Backtracks as far as possible for the derived clause to be propagating.
    ///
    /// This also reorders the literals of the derived clause such that after backtracking the first
    /// literal is unassigned and the second literal has the highest trail index of the remaining
    /// literals.
    fn backtrack(&mut self) {
        // Move the literal propagated after backtracing to index 0 (unit propagation invariant).
        let derived_clause_len = self.data.derived_clause.len();
        self.data.derived_clause.swap(0, derived_clause_len - 1);

        let mut backtrack_level = 0;

        if derived_clause_len > 1 {
            // Of the remaining literals move the one with the largest trail index to index 1
            // (maintains unit propagation invariant on further backtracking).
            let mut largest_trail_index = self.trail.trail_index(self.data.derived_clause[1].var());
            for i in 2..derived_clause_len {
                let trail_index = self.trail.trail_index(self.data.derived_clause[i].var());
                if trail_index > largest_trail_index {
                    largest_trail_index = trail_index;
                    self.data.derived_clause.swap(1, i);
                }
            }

            backtrack_level = self.trail.steps()[largest_trail_index].decision_level;
        }

        self.trail.backtrack_to_level(backtrack_level);
    }

    /// Derives the 1-UIP clause from the implication graph and the given conflict.
    ///
    /// The derived clause is stored in `self.data.derived_clause`. The UIP will be the last literal
    /// of the derived clause.
    fn derive_1uip_clause(&mut self, conflict: ConflictClause) {
        self.data.derived_clause.clear();

        self.data.update_trail_len(self.trail.steps().len());

        // Here we learn a new 1-UIP clause from the conflict

        // We start with the conflict clause itself:
        for &lit in conflict.lits(&self.clauses) {
            Self::add_literal(&mut self.data, self.trail, lit);
        }

        // As long as there are multiple literals of the current decision level in the current
        // clause we resolve it to eventually reduce that number to one. The current clause remains
        // in conflict throughout.

        // The initial conflict clause always has at leat two such literals as it would have
        // propageted at an earlier decision level otherwise.
        for trail_index in (0..self.trail.steps().len()).rev() {
            // We identify the last assigned literal (by scanning the trail backwards) of the
            // current decision level contained in the current clause.

            // TODO this assumes all encountered literals up to the 1-UIP are at the current
            // decision level, which is true because the assignments of the current decision level
            // are a suffix of the trail. This is no longer true if chronological backtracking is
            // implemented!

            // If the corresponding literal is in the current clause remove it. (We will either
            // resolve on it or place it back when we are done.)
            if !replace(&mut self.data.current_clause_lits[trail_index], false) {
                continue;
            }

            let step = &self.trail.steps()[trail_index];

            self.data.current_level_lit_count -= 1;
            if self.data.current_level_lit_count == 0 {
                // If this was the last literal at the current decision level we found a 1-UIP
                // clause. We clear `current_clause_lits` and add the corresponding literal to
                // `derived_clause` without resolving on it.
                for &lit in &self.data.derived_clause {
                    let trail_index = self.trail.trail_index(lit.var());
                    self.data.current_clause_lits[trail_index] = false;
                }
                self.data.derived_clause.push(!step.assigned_lit);
                break;
            } else {
                // We resolve the current clause on the literal at `trail_index`. We already removed
                // that literal from the current clause, so we only need to add the asserting
                // literals to get the resolvent.
                for &asserting_lit in step.reason.lits(self.clauses) {
                    Self::add_literal(&mut self.data, self.trail, asserting_lit);
                }
            }
        }

        assert_eq!(self.data.current_level_lit_count, 0);
    }

    /// Adds a literal to the current clause.
    ///
    /// Ignores literals of decision level 0 as they are always false and can be removed by
    /// resolving them with the corresponding (implied) unit clause.
    ///
    /// Otherwise, if the literal is not of the current decision level it is directly added to the
    /// `derived_clause`. If it is of the current decision level, the corresponding counter is
    /// updated.
    fn add_literal(data: &mut ConflictAnalysisData, trail: &Trail, lit: Lit) {
        let trail_index = trail.trail_index(lit.var());
        let lit_decision_level = trail.steps()[trail_index].decision_level;
        // If the literal is assigned at level zero, it is always falsified and we can directly
        // remove it.
        if lit_decision_level == 0 {
            return;
        }
        // If the literal is already added, don't add it a second time.
        if replace(&mut data.current_clause_lits[trail_index], true) {
            return;
        }
        if lit_decision_level == trail.decision_level() {
            // If the literal is assigned at the current decision level, we may want
            // to resolve on it.
            data.current_level_lit_count += 1;
        } else {
            // If the literal is assigned at a non-zero decision level, we will not
            // resolve on it so it will be part of the derived clause.
            data.derived_clause.push(lit);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{lit::Var, tracking::TracksVarCount, unit_prop::UnitProp};

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
                clauses.add_clause(&[$(Lit::from_dimacs($lit)),*]);
            )*
            clauses
        }};
    }

    macro_rules! trail {
        ($clauses:ident) => {{
            let mut trail = Trail::default();
            trail.set_var_count($clauses.var_count());
            trail
        }};
    }

    #[test]
    fn unit_clause() {
        let mut clauses = clauses![4 vars
            -1, 2;
            -1, 3;
            -2, -3;
            -4, 1;
        ];
        let mut trail = trail!(clauses);
        let mut data = ConflictAnalysisData::default();

        trail.assign_decision(Lit::from_dimacs(4));

        let conflict = UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap_err();

        ConflictAnalysis {
            trail: &mut trail,
            clauses: &mut clauses,
            data: &mut data,
        }
        .analyze_conflict(conflict);

        assert_eq!(data.derived_clause, &clause![-1]);

        UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap();

        assert!(trail.assigned.is_true(Lit::from_dimacs(-1)));
        assert_eq!(trail.step_for_var(Var::from_dimacs(1)).reason, Reason::Unit);
        assert!(trail.assigned.is_true(Lit::from_dimacs(-4)));
    }

    #[test]
    fn long_clause() {
        let mut clauses = clauses![7 vars
            -1, 2;
            -1, 3;
            -2, -3, -4, -5;
            -6, 7;
            -7, 4;
            -7, 5;
        ];
        let mut trail = trail!(clauses);
        let mut data = ConflictAnalysisData::default();

        trail.assign_decision(Lit::from_dimacs(1));

        UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap();

        trail.assign_decision(Lit::from_dimacs(6));

        let conflict = UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap_err();

        ConflictAnalysis {
            trail: &mut trail,
            clauses: &mut clauses,
            data: &mut data,
        }
        .analyze_conflict(conflict);

        UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .ok()
        .unwrap();

        assert!(trail.assigned.is_true(Lit::from_dimacs(-7)));
        if let Reason::Long(clause) = trail.step_for_var(Var::from_dimacs(7)).reason {
            assert_eq!(clauses.long.lits(clause), data.derived_clause);
            data.derived_clause.sort_unstable(); // not used below, we can clobber it
            assert_eq!(data.derived_clause, &clause![-2, -3, -7]);
        } else {
            panic!("expected a long clause")
        }
        assert!(trail.assigned.is_true(Lit::from_dimacs(-6)));
    }

    #[test]
    fn binary_clause() {
        let mut clauses = clauses![7 vars
            -1, 2;
            -1, 3;
            -2, -4, -5;
            -6, 7;
            -7, 4;
            -7, 5;
        ];
        let mut trail = trail!(clauses);
        let mut data = ConflictAnalysisData::default();

        trail.assign_decision(Lit::from_dimacs(1));

        UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap();

        trail.assign_decision(Lit::from_dimacs(6));

        let conflict = UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .unwrap_err();

        ConflictAnalysis {
            trail: &mut trail,
            clauses: &mut clauses,
            data: &mut data,
        }
        .analyze_conflict(conflict);

        UnitProp {
            trail: &mut trail,
            clauses: &mut clauses,
        }
        .propagate()
        .ok()
        .unwrap();

        assert!(trail.assigned.is_true(Lit::from_dimacs(-7)));
        assert_eq!(
            trail.step_for_var(Var::from_dimacs(7)).reason,
            Reason::Binary(Lit::from_dimacs(-2))
        );

        data.derived_clause.sort_unstable(); // not used below, we can clobber it
        assert_eq!(data.derived_clause, &clause![-2, -7]);
        assert!(trail.assigned.is_true(Lit::from_dimacs(-6)));
    }
}
