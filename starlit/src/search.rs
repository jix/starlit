//! CDCL search data structures.

use crate::{
    conflict_analysis::{analyze_conflict, ConflictAnalysis, ConflictAnalysisCallbacks},
    context::Ctx,
    lit::{Lit, Var},
    prop::{
        collect_garbage,
        trail::{assign_decision, backtrack_to_level, BacktrackCallbacks, DecisionLevel},
        unit_prop::propagate,
        Prop,
    },
    tracking::Resize,
};

use self::{phases::Phases, vsids::Vsids};

mod phases;
mod reduce;
mod vsids;

/// CDCL search data structures.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Search {
    pub prop: Prop,
    pub conflict_analysis: ConflictAnalysis,
    pub vsids: Vsids,
    pub phases: Phases,
}

impl Resize for Search {
    fn resize(&mut self, var_count: usize) {
        self.prop.resize(var_count);
        self.vsids.resize(var_count);
        self.phases.resize(var_count);
    }
}

/// Performs one step of CDCL search and returns whether the formula is satisfiable.
pub fn search_step(ctx: &mut Ctx, search: &mut Search) -> Option<bool> {
    if search.prop.unsat {
        return Some(false);
    }
    collect_garbage(ctx, &mut search.prop);

    // Propagate with the current assignment
    let prop_result = propagate(ctx, &mut search.prop);

    if let Err(conflict) = prop_result {
        ctx.stats.search.conflicts += 1;
        if search.prop.trail.decision_level() == DecisionLevel::TOP {
            search.prop.unsat = true;
            // Conflict without any assumptions means the formula is UNSAT
            verbose!(ctx, "unsatisfiable");

            return Some(false);
        }
        // Otherwise we can learn an asserting clause and backtrack to the level where it turns from
        // in-conflict to asserting.
        analyze_conflict(
            ctx,
            &mut search.conflict_analysis,
            &mut search.prop,
            conflict,
            &mut Callbacks {
                vsids: &mut search.vsids,
                phases: &mut search.phases,
            },
        );
    } else if let Some(var) = search.vsids.pop_decision_var(&search.prop.values) {
        // When there was no conflict but not all variables are assigned, make a heuristic
        // decision.
        ctx.stats.search.decisions += 1;
        let lit = search.phases.decide_phase(var);
        trace!(ctx, decision = lit);
        assign_decision(&mut search.prop, lit);
    } else {
        // All variables are assigned and unit propagation reported no conflict so the
        // current assignment is a full satisfying assignment.
        verbose!(ctx, "satisfiable");
        return Some(true);
    }

    None
}

struct Callbacks<'a> {
    pub vsids: &'a mut Vsids,
    pub phases: &'a mut Phases,
}

impl<'a> BacktrackCallbacks for Callbacks<'a> {
    fn unassign(&mut self, lit: Lit) {
        self.vsids.unassign(lit);
        self.phases.unassign(lit);
    }
}

impl<'a> ConflictAnalysisCallbacks for Callbacks<'a> {
    fn var_in_conflict(&mut self, var: Var) {
        self.vsids.bump_var(var);
    }

    fn analyzed_conflict(&mut self) {
        self.vsids.decay();
    }
}

/// Performs a restart by backtracking to decision level 0.
pub fn restart(ctx: &mut Ctx, search: &mut Search) {
    debug!(ctx, "restart");
    ctx.stats.search.restarts += 1;

    if search.prop.trail.decision_level() > DecisionLevel::TOP {
        backtrack_to_level(
            ctx,
            &mut search.prop,
            DecisionLevel::TOP,
            &mut Callbacks {
                vsids: &mut search.vsids,
                phases: &mut search.phases,
            },
        )
    }
}

pub use reduce::reduce;

/// Statistics for the CDCL search.
#[derive(Default, Debug)]
pub struct SearchStats {
    /// Total number of decisions.
    pub decisions: u64,
    /// Total number of conflicts.
    pub conflicts: u64,
    /// Total number of restarts.
    pub restarts: u64,
    /// Total number of reductions.
    pub reductions: u64,
}
