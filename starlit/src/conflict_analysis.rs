//! Conflict analysis.
use std::mem::replace;

use crate::{
    clause_arena::ClauseRef,
    context::Ctx,
    glue::compute_glue,
    lit::{Lit, Var},
    minimize,
    minimize::MinimizeClause,
    prop::{
        add_clause_verbatim,
        long::{LongClauses, LongHeader},
        trail::{
            assign, backtrack_to_level, BacktrackCallbacks, DecisionLevel, Reason, Step, Trail,
            TrailIndex,
        },
        ConflictClause, Prop,
    },
    util::vec_map::VecMap,
};

/// Callbacks to update state related to conflict analysis.
pub trait ConflictAnalysisCallbacks: BacktrackCallbacks {
    /// Called for each variable on the conflict side during analysis.
    fn var_in_conflict(&mut self, _var: Var) {}

    /// Called after a conflict was analyzed, before backtracing and learning.
    fn analyzed_conflict(&mut self) {}
}

impl ConflictAnalysisCallbacks for () {}

/// Data used exclusively during conflict analysis.
#[derive(Default)]
pub struct ConflictAnalysis {
    /// Literals of the current conflicting clause.
    ///
    /// Every true value corresponds to the literal assigned in the trail step of the same index.
    ///
    /// This is initialized to the literals of the conflict clause and is modified by successively
    /// resolving it with the reason for falsifying a contained literal until an asserting 1-UIP
    /// clause is found.
    current_clause_lits: VecMap<TrailIndex, bool>,

    /// Temporary decision level flags for glue computation.
    glue_level_flags: VecMap<DecisionLevel, bool>,

    /// Literals of the final derived asserting clause.
    ///
    /// Before a 1-UIP clause is found, this only contains literals below the current decision
    /// level.
    derived_clause: Vec<Lit>,

    /// Number of literals of the current decision level in the current conflicting clause.
    current_level_lit_count: usize,

    /// Learned clause minimization data
    minimize_clause: MinimizeClause,
}

impl ConflictAnalysis {
    /// Reserves enough buffer space for analyzing the current conflict.
    fn update_trail_len(&mut self, trail: &Trail) {
        let new_len = self.current_clause_lits.len().max(trail.steps().len());
        self.current_clause_lits.resize(new_len, false);

        let new_len = self
            .glue_level_flags
            .len()
            .max(trail.decision_level().0 as usize + 1);
        self.glue_level_flags.resize(new_len, false);
    }
}

/// Analyzes a conflict, learning a new clause that avoids that conflict in the future.
///
/// This derives an asserting 1-UIP clause and backtracks such that the new clause is no longer
/// in conflict, but instead propagates a new assignment.
///
/// This only propagates a single new literal and needs to be followed by unit propagation.
pub fn analyze_conflict(
    ctx: &mut Ctx,
    analysis: &mut ConflictAnalysis,
    prop: &mut Prop,
    conflict: ConflictClause,
    callbacks: &mut impl ConflictAnalysisCallbacks,
) {
    assert_ne!(prop.trail.decision_level(), DecisionLevel::TOP);

    derive_1uip_clause(ctx, analysis, prop, conflict, callbacks);
    callbacks.analyzed_conflict();

    // TODO make this configurable
    let backtrack_level = if true {
        minimize_derived_clause(analysis, prop)
    } else {
        prepare_for_backtracking(analysis, prop)
    };

    backtrack_to_level(ctx, prop, backtrack_level, callbacks);

    learn_and_assign(ctx, analysis, prop);
}

/// Derives the 1-UIP clause from the implication graph and the given conflict.
///
/// The derived clause is stored in `self.data.derived_clause`. The UIP will be the last literal
/// of the derived clause.
fn derive_1uip_clause(
    ctx: &mut Ctx,
    analysis: &mut ConflictAnalysis,
    prop: &mut Prop,
    conflict: ConflictClause,
    callbacks: &mut impl ConflictAnalysisCallbacks,
) {
    analysis.derived_clause.clear();

    analysis.update_trail_len(&prop.trail);

    // Here we learn a new 1-UIP clause from the conflict

    // We start with the conflict clause itself:
    if let ConflictClause::Long(conflict) = conflict {
        bump_long_clause(
            &prop.trail,
            &mut prop.long,
            conflict,
            &mut analysis.glue_level_flags,
        );
    }
    for &lit in conflict.lits(prop) {
        add_literal(analysis, &prop.trail, lit, callbacks);
    }

    // As long as there are multiple literals of the current decision level in the current
    // clause we resolve it to eventually reduce that number to one. The current clause remains
    // in conflict throughout.

    // The initial conflict clause always has at leat two such literals as it would have
    // propageted at an earlier decision level otherwise.
    for trail_index in prop.trail.steps().keys().rev() {
        // We identify the last assigned literal (by scanning the trail backwards) of the
        // current decision level contained in the current clause.

        // TODO this assumes all encountered literals up to the 1-UIP are at the current
        // decision level, which is true because the assignments of the current decision level
        // are a suffix of the trail. This is no longer true if chronological backtracking is
        // implemented!

        // If the corresponding literal is in the current clause remove it. (We will either
        // resolve on it or place it back when we are done.)
        if !replace(&mut analysis.current_clause_lits[trail_index], false) {
            continue;
        }

        let step = &prop.trail.steps()[trail_index];

        analysis.current_level_lit_count -= 1;
        if analysis.current_level_lit_count == 0 {
            // If this was the last literal at the current decision level we found a 1-UIP
            // clause. We clear `current_clause_lits` and add the corresponding literal to
            // `derived_clause` without resolving on it.
            for &lit in &analysis.derived_clause {
                let trail_index = prop.trail.trail_index(lit.var());
                analysis.current_clause_lits[trail_index] = false;
            }
            analysis.derived_clause.push(!step.assigned_lit);
            break;
        } else {
            // We resolve the current clause on the literal at `trail_index`. We already removed
            // that literal from the current clause, so we only need to add the asserting
            // literals to get the resolvent.
            if let Reason::Long(reason) = step.reason {
                bump_long_clause(
                    &prop.trail,
                    &mut prop.long,
                    reason,
                    &mut analysis.glue_level_flags,
                );
            }
            for &asserting_lit in step.reason.lits(prop) {
                add_literal(analysis, &prop.trail, asserting_lit, callbacks);
            }
        }
    }

    assert_eq!(analysis.current_level_lit_count, 0);

    trace!(ctx, "1-uip", clause = analysis.derived_clause);
}

fn bump_long_clause(
    trail: &Trail,
    long: &mut LongClauses,
    clause: ClauseRef,
    tmp: &mut VecMap<DecisionLevel, bool>,
) {
    let (header, lits) = long.header_and_lits_mut(clause);
    header.set_glue(compute_glue(trail, lits, tmp));
    header.set_used(header.used() + 1);
}

/// Adds a literal to the current clause.
///
/// Ignores literals of decision level 0 as they are always false and can be removed by
/// resolving them with the corresponding (implied) unit clause.
///
/// Otherwise, if the literal is not of the current decision level it is directly added to the
/// `derived_clause`. If it is of the current decision level, the corresponding counter is
/// updated.
fn add_literal(
    analysis: &mut ConflictAnalysis,
    trail: &Trail,
    lit: Lit,
    callbacks: &mut impl ConflictAnalysisCallbacks,
) {
    let trail_index = trail.trail_index(lit.var());
    let lit_decision_level = trail.steps()[trail_index].decision_level;
    // If the literal is assigned at level zero, it is always falsified and we can directly
    // remove it.
    if lit_decision_level == DecisionLevel::TOP {
        return;
    }
    // If the literal is already added, don't add it a second time.
    if replace(&mut analysis.current_clause_lits[trail_index], true) {
        return;
    }
    callbacks.var_in_conflict(lit.var());
    if lit_decision_level == trail.decision_level() {
        // If the literal is assigned at the current decision level, we may want
        // to resolve on it.
        analysis.current_level_lit_count += 1;
    } else {
        // If the literal is assigned at a non-zero decision level, we will not
        // resolve on it so it will be part of the derived clause.
        analysis.derived_clause.push(lit);
    }
}

/// Determines the backtrack level required for the derived clause to be propagating.
///
/// This also reorders the literals of the derived clause such that after backtracking the first
/// literal is unassigned and the second literal has the highest trail index of the remaining
/// literals.
fn prepare_for_backtracking(analysis: &mut ConflictAnalysis, prop: &mut Prop) -> DecisionLevel {
    // Move the literal propagated after backtracing to index 0 (unit propagation invariant).
    let derived_clause_len = analysis.derived_clause.len();
    analysis.derived_clause.swap(0, derived_clause_len - 1);

    let mut backtrack_level = DecisionLevel::TOP;

    if derived_clause_len > 1 {
        // Of the remaining literals move the one with the largest trail index to index 1
        // (maintains unit propagation invariant on further backtracking).
        let mut largest_trail_index = prop.trail.trail_index(analysis.derived_clause[1].var());
        for i in 2..derived_clause_len {
            let trail_index = prop.trail.trail_index(analysis.derived_clause[i].var());
            if trail_index > largest_trail_index {
                largest_trail_index = trail_index;
                analysis.derived_clause.swap(1, i);
            }
        }

        backtrack_level = prop.trail.steps()[largest_trail_index].decision_level;
    }
    backtrack_level
}

fn minimize_derived_clause(analysis: &mut ConflictAnalysis, prop: &mut Prop) -> DecisionLevel {
    if analysis.derived_clause.len() > 1 {
        minimize::minimize(
            &mut analysis.minimize_clause,
            &mut analysis.derived_clause,
            prop,
        )
    } else {
        DecisionLevel::TOP
    }
}

/// Adds the derived clause to the current formula and assign the newly asserted literal.
fn learn_and_assign(ctx: &mut Ctx, analysis: &mut ConflictAnalysis, prop: &mut Prop) {
    #[cfg(debug_assertions)]
    for &lit in &analysis.derived_clause[1..] {
        debug_assert!(prop.values.is_false(lit));
    }

    let mut header = LongHeader::new_learned_clause();

    if analysis.derived_clause.len() > 2 {
        header.set_glue(compute_glue(
            &prop.trail,
            &analysis.derived_clause[1..],
            &mut analysis.glue_level_flags,
        ));
    }

    if let Some(proof) = &mut ctx.proof {
        proof.add_clause(&analysis.derived_clause)
    }

    // TODO add and use a clause addition function that handles propagation

    let reason = match add_clause_verbatim(ctx, prop, header, &analysis.derived_clause) {
        crate::prop::AddedClause::Empty => None,
        crate::prop::AddedClause::Unit(_) => None,
        crate::prop::AddedClause::Binary([_, b]) => Some(Reason::Binary(b)),
        crate::prop::AddedClause::Long(clause) => Some(Reason::Long(clause)),
    };

    if let Some(reason) = reason {
        assign(
            prop,
            Step {
                assigned_lit: analysis.derived_clause[0],
                decision_level: prop.trail.decision_level(),
                reason,
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lit::Var,
        prop::{trail::assign_decision, unit_prop::propagate, Prop},
        tracking::Resize,
    };

    use super::*;

    macro_rules! clause {
        ($($lit:literal),* $(,)?) => {{
            [$(Lit::from_dimacs($lit)),*]
        }};
    }

    macro_rules! clauses {
        ($ctx:expr, $var_count:literal vars $($($lit:literal),+);* $(;)?) => {{
            let mut prop = Prop::default();
            prop.resize($var_count);
            $(
                add_clause_verbatim(
                    &mut $ctx,
                    &mut prop,
                    LongHeader::new_input_clause(),
                    &[$(Lit::from_dimacs($lit)),*],
                );
            )*
            prop
        }};
    }
    #[test]
    fn unit_clause() {
        let mut ctx = Ctx::default();
        let mut prop = clauses![ctx, 4 vars
            -1, 2;
            -1, 3;
            -2, -3;
            -4, 1;
        ];
        let mut data = ConflictAnalysis::default();

        assign_decision(&mut prop, Lit::from_dimacs(4));

        let conflict = propagate(&mut ctx, &mut prop).unwrap_err();

        analyze_conflict(&mut ctx, &mut data, &mut prop, conflict, &mut ());

        assert_eq!(data.derived_clause, &clause![-1]);

        propagate(&mut ctx, &mut prop).unwrap();

        assert!(prop.values.is_true(Lit::from_dimacs(-1)));
        assert_eq!(
            prop.trail.step_for_var(Var::from_dimacs(1)).reason,
            Reason::Unit
        );
        assert!(prop.values.is_true(Lit::from_dimacs(-4)));
    }

    #[test]
    fn long_clause() {
        let mut ctx = Ctx::default();
        let mut prop = clauses![ctx, 7 vars
            -1, 2;
            -1, 3;
            -2, -3, -4, -5;
            -6, 7;
            -7, 4;
            -7, 5;
        ];
        let mut data = ConflictAnalysis::default();

        assign_decision(&mut prop, Lit::from_dimacs(1));

        propagate(&mut ctx, &mut prop).unwrap();

        assign_decision(&mut prop, Lit::from_dimacs(6));

        let conflict = propagate(&mut ctx, &mut prop).unwrap_err();

        analyze_conflict(&mut ctx, &mut data, &mut prop, conflict, &mut ());

        propagate(&mut ctx, &mut prop).ok().unwrap();

        assert!(prop.values.is_true(Lit::from_dimacs(-7)));
        if let Reason::Long(clause) = prop.trail.step_for_var(Var::from_dimacs(7)).reason {
            assert_eq!(prop.long.lits(clause), data.derived_clause);
            data.derived_clause.sort_unstable(); // not used below, we can clobber it
            assert_eq!(data.derived_clause, &clause![-2, -3, -7]);
        } else {
            panic!("expected a long clause")
        }
        assert!(prop.values.is_true(Lit::from_dimacs(-6)));
    }

    #[test]
    fn binary_clause() {
        let mut ctx = Ctx::default();
        let mut prop = clauses![ctx, 7 vars
            -1, 2;
            -1, 3;
            -2, -4, -5;
            -6, 7;
            -7, 4;
            -7, 5;
        ];
        let mut data = ConflictAnalysis::default();

        assign_decision(&mut prop, Lit::from_dimacs(1));

        propagate(&mut ctx, &mut prop).unwrap();

        assign_decision(&mut prop, Lit::from_dimacs(6));

        let conflict = propagate(&mut ctx, &mut prop).unwrap_err();

        analyze_conflict(&mut ctx, &mut data, &mut prop, conflict, &mut ());

        propagate(&mut ctx, &mut prop).ok().unwrap();

        assert!(prop.values.is_true(Lit::from_dimacs(-7)));
        assert_eq!(
            prop.trail.step_for_var(Var::from_dimacs(7)).reason,
            Reason::Binary(Lit::from_dimacs(-2))
        );

        data.derived_clause.sort_unstable(); // not used below, we can clobber it
        assert_eq!(data.derived_clause, &clause![-2, -7]);
        assert!(prop.values.is_true(Lit::from_dimacs(-6)));
    }
}
