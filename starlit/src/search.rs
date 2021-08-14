//! CDCL search.
use crate::{
    clauses::{long::ClauseRefGcMap, Clauses},
    conflict_analysis::{ConflictAnalysis, ConflictAnalysisCallbacks, ConflictAnalysisOps},
    decision::vsids::Vsids,
    lit::{Lit, Var},
    phases::Phases,
    tracking::TracksVarCount,
    trail::{BacktrackCallbacks, DecisionLevel, Trail},
    unit_prop::{UnitProp, UnitPropOps},
};

/// CDCL search data structures.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Search {
    pub trail: Trail,
    pub clauses: Clauses,
    pub unit_prop: UnitProp,
    pub conflict_analysis: ConflictAnalysis,
    pub vsids: Vsids,
    pub phases: Phases,
    pub stats: SearchStats,
}

impl TracksVarCount for Search {
    fn var_count(&self) -> usize {
        self.trail.var_count()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.trail.set_var_count(var_count);
        self.clauses.set_var_count(var_count);
        self.vsids.set_var_count(var_count);
        self.phases.set_var_count(var_count);
    }
}

impl Search {
    /// Performs one step of CDCL search and returns whether the formula is satisfiable.
    pub fn search_step(&mut self) -> Option<bool> {
        self.collect_garbage();

        let previously_propagated = self.unit_prop.propagated;

        let mut unit_prop = UnitPropOps {
            trail: &mut self.trail,
            clauses: &mut self.clauses,
            unit_prop: &mut self.unit_prop,
        };

        // Propagate with the current assignment
        let prop_result = unit_prop.propagate();
        self.stats.propagations += (self.unit_prop.propagated - previously_propagated) as u64;
        if let Err(conflict) = prop_result {
            self.stats.conflicts += 1;
            if self.trail.decision_level() == DecisionLevel::TOP {
                // Conflict without any assumptions means the formula is UNSAT
                tracing::debug!("UNSAT");
                return Some(false);
            }
            // Otherwise we can learn from the conflict and backtrack
            let mut conflict_analysis = ConflictAnalysisOps {
                trail: &mut self.trail,
                clauses: &mut self.clauses,
                conflict_analysis: &mut self.conflict_analysis,
            };

            // Learns an asserting clause and backtracks to the level where it turns from
            // in-conflict to asserting.
            conflict_analysis.analyze_conflict(
                conflict,
                &mut Callbacks {
                    unit_prop: &mut self.unit_prop,
                    vsids: &mut self.vsids,
                    phases: &mut self.phases,
                },
            );
        } else if let Some(var) = self.vsids.pop_decision_var(&self.trail.assigned) {
            // When there was no conflict but not all variables are assigned, make a heuristic
            // decision.
            self.stats.decisions += 1;
            let lit = self.phases.decide_phase(var);
            tracing::trace!(?lit, "decision");
            self.trail.assign_decision(lit);
        } else {
            // All variables are assigned and unit propagation reported no conflict so the
            // current assignment is a full satisfying assignment.
            tracing::debug!("SAT");
            return Some(true);
        }

        None
    }

    /// Performs a restart by backtracking to decision level 0.
    pub fn restart(&mut self) {
        tracing::debug!("restart");
        if self.trail.decision_level() > DecisionLevel::TOP {
            self.trail.backtrack_to_level(
                DecisionLevel::TOP,
                &mut Callbacks {
                    unit_prop: &mut self.unit_prop,
                    vsids: &mut self.vsids,
                    phases: &mut self.phases,
                },
            )
        }
    }

    /// Perfoms garbage collection when necessary.
    pub fn collect_garbage(&mut self) -> Option<ClauseRefGcMap> {
        self.clauses
            .long
            .should_collect_garbage()
            .then(|| self.collect_garbage_now())
    }

    /// Unconditionally performs garbage collection.
    fn collect_garbage_now(&mut self) -> ClauseRefGcMap {
        tracing::debug!("garbage collection");
        let gc_map = self.clauses.long.collect_garbage();

        self.trail.update_clause_references(&gc_map);

        self.clauses.watch_lists.update_clause_references(&gc_map);
        // TODO alternatively:
        // self.clauses.enable_watch_lists(false);
        gc_map
    }
}

struct Callbacks<'a> {
    pub unit_prop: &'a mut UnitProp,
    pub vsids: &'a mut Vsids,
    pub phases: &'a mut Phases,
}

impl<'a> BacktrackCallbacks for Callbacks<'a> {
    fn unassign(&mut self, lit: Lit) {
        self.vsids.unassign(lit);
        self.phases.unassign(lit);
    }

    fn backtracked(&mut self, trail: &Trail) {
        self.unit_prop.backtracked(trail);
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

/// Statistics for the CDCL search.
#[derive(Default, Debug)]
pub struct SearchStats {
    /// Total number of decisions.
    pub decisions: u64,
    /// Total number of conflicts.
    pub conflicts: u64,
    /// Total number of propagated assignments.
    pub propagations: u64,
}
