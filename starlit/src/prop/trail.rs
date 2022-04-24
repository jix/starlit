//! Stores a history of steps performed during the search to enable backtracking.
use crate::{
    clause_arena::{ClauseRef, ClauseRefGcMap},
    lit::{Lit, LitIdx, Var},
    partial_assignment::PartialAssignment,
    tracking::Resize,
    util::vec_map::{VecMap, VecMapIndex, VecMapKey},
};

use super::Prop;

/// A decision level.
///
/// Wrapper around `LitIdx` for better type safety.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct DecisionLevel(pub LitIdx);

impl DecisionLevel {
    /// The top decision level that contains unconditional assignments.
    pub const TOP: DecisionLevel = DecisionLevel(0);
}

impl std::fmt::Debug for DecisionLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

impl VecMapIndex for DecisionLevel {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        self.0 as usize
    }
}

impl VecMapKey for DecisionLevel {
    #[inline(always)]
    fn vec_map_key_from_index(index: usize) -> Self {
        Self(index as _)
    }
}

/// A position on the trail.
///
/// When processing the implication graph it is often convenient to refer to literals by their
/// position on the trail. Using this type instead of an integer make this more type safe and helps
/// avoiding casts between `usize` and `LitIdx`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TrailIndex(pub LitIdx);

impl TrailIndex {
    // How I wish there was a `NotMaxU32` type or some other way to specify custom niche values...
    /// Marker for variables that are unassigned.
    ///
    /// Note that `Trail::trail_index` is only valid for assigned variables and is not guaranteed to
    /// return this for unassigned variables.
    pub const UNASSIGNED: TrailIndex = TrailIndex(LitIdx::MAX);
}

impl std::fmt::Debug for TrailIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

impl VecMapIndex for TrailIndex {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        self.0 as usize
    }
}

impl VecMapKey for TrailIndex {
    #[inline(always)]
    fn vec_map_key_from_index(index: usize) -> Self {
        Self(index as _)
    }
}

/// The reason for an assignment, represents edges of the implication graph.
#[derive(Eq, PartialEq, Debug)]
pub enum Reason {
    /// Assigned as decision literal.
    Decision,
    /// Implied by a unit clause.
    Unit,
    /// Impled by a binary clause because the given literal is false.
    Binary(Lit),
    /// Implied by a long clause because all but its first literal are false.
    Long(ClauseRef),
}

impl Reason {
    /// Returns the falsified literals the cause the propagation.
    pub fn lits<'a>(&'a self, prop: &'a Prop) -> &'a [Lit] {
        match self {
            Reason::Decision | Reason::Unit => &[],
            Reason::Binary(lit) => std::slice::from_ref(lit),
            Reason::Long(clause) => {
                // Unit propagation ensures that the falsified literals are contiguous.
                &prop.long.lits(*clause)[1..]
            }
        }
    }
}

/// A step of the trail.
pub struct Step {
    /// The assigned literal.
    pub assigned_lit: Lit,
    /// The decision level of this step.
    ///
    /// The decision level of the `n`-th decision literal is `n`. For a propagated literal the
    /// decision level is the maximum decision level among the falsified literals in the propagating
    /// clause or zero if there are none.
    pub decision_level: DecisionLevel,
    /// The propagating clause that assigned this literal.
    ///
    /// Used to represent the implication graph.
    pub reason: Reason,
}

/// Stores a history of steps performed during the search to enable backtracking.
///
/// This also contains the implication graph.
pub struct Trail {
    /// The step on which a variable was assigned.
    trail_index: VecMap<Var, TrailIndex>,

    /// Sequence of performed steps.
    steps: VecMap<TrailIndex, Step>,

    /// Number of steps that are fully propagated.
    propagated: usize,

    /// Trail indices of decisions.
    ///
    /// The first entry does not represent a decision and is fixed at 0 so that each entry on the
    /// trail has a preceding entry in this list and so that the decision at level `n` corresponds
    /// to the index `n`.
    decisions: Vec<LitIdx>,
}

impl Default for Trail {
    fn default() -> Self {
        Trail {
            trail_index: VecMap::default(),
            steps: VecMap::default(),
            propagated: 0,
            decisions: vec![0],
        }
    }
}

impl Resize for Trail {
    fn resize(&mut self, var_count: usize) {
        self.trail_index.resize(var_count, TrailIndex::UNASSIGNED)
    }
}

impl Trail {
    /// Number of decisions made.
    pub fn decision_level(&self) -> DecisionLevel {
        DecisionLevel((self.decisions.len() - 1) as LitIdx)
    }

    /// Returns the history of performed assignment steps.
    pub fn steps(&self) -> &VecMap<TrailIndex, Step> {
        &self.steps
    }

    /// Returns the index of the step that assigned a given variable.
    ///
    /// With debug assertions enabled, this will panic if the variable is not assigned by a step on
    /// the trail. For release builds, calling this for an unassigned variable might panic or return
    /// bogus data. It is memory safe in either case.
    pub fn trail_index(&self, var: Var) -> TrailIndex {
        let index = self.trail_index[var];
        debug_assert_ne!(index, TrailIndex::UNASSIGNED);
        index
    }

    /// Returns the step that assigned a given variable.
    ///
    /// With debug assertions enabled, this will panic if the variable is not assigned by a step on
    /// the trail. For release builds, calling this for an unassigned variable might panic or return
    /// bogus data. It is memory safe in either case.
    pub fn step_for_var(&self, var: Var) -> &Step {
        &self.steps[self.trail_index(var)]
    }

    /// Updates refrence to long clauses after garbage collection.
    pub fn update_clause_references(&mut self, gc_map: &ClauseRefGcMap) {
        for step in &mut *self.steps {
            if let Reason::Long(clause) = &mut step.reason {
                *clause = gc_map.update(*clause).unwrap();
            }
        }
    }

    /// Returns the first literal that is not known to be fully propagted.
    pub fn next_unpropagated_lit(&self) -> Option<Lit> {
        self.steps
            .get(self.propagated)
            .map(|step| step.assigned_lit)
    }

    /// Marks the next literal as fully propagated.
    pub fn advance_propagated(&mut self) {
        debug_assert!(self.propagated < self.steps.len());
        self.propagated += 1
    }

    /// Number of literals on the trail that are known to be fully propagated.
    pub fn propagated(&self) -> usize {
        self.propagated
    }
}

/// Same as [`assign`] but can be called when borrowing other parts of [`Prop`].
pub fn assign_raw(values: &mut PartialAssignment, trail: &mut Trail, step: Step) {
    trail.trail_index[step.assigned_lit] = TrailIndex(trail.steps.len() as _);
    debug_assert!(!values.is_assigned(step.assigned_lit.var()));
    values.assign(step.assigned_lit);
    trail.steps.push(step);
}

/// Adds a step that to the trail and assign the corresponding literal.
pub fn assign(prop: &mut Prop, step: Step) {
    assign_raw(&mut prop.values, &mut prop.trail, step)
}

/// Assign a decision and add the corresponding step to the trail.
pub fn assign_decision(prop: &mut Prop, lit: Lit) {
    prop.trail.decisions.push(prop.trail.steps.len() as LitIdx);
    assign(
        prop,
        Step {
            assigned_lit: lit,
            decision_level: prop.trail.decision_level(),
            reason: Reason::Decision,
        },
    )
}

/// Callbacks to synchronize state with backtracking on the trail.
pub trait BacktrackCallbacks {
    /// Called before undoing the assignment `lit`.
    fn unassign(&mut self, _lit: Lit) {}
}

impl BacktrackCallbacks for () {}

/// Bactracks to a given decision level.
///
/// This undoes all assignments of a higher decision level.
///
/// Panics if the target decision level is the current decision level or higher.
pub fn backtrack_to_level(
    prop: &mut Prop,
    decision_level: DecisionLevel,
    callbacks: &mut impl BacktrackCallbacks,
) {
    // tracing::trace!(?decision_level, "backtrack");
    assert!(decision_level < prop.trail.decision_level());

    // Get the index corresponding to the lowest decision to undo
    let target_trail_len = prop.trail.decisions[decision_level.0 as usize + 1] as usize;

    for step in prop.trail.steps.drain(target_trail_len..) {
        let lit = step.assigned_lit;
        // Undo the assignment
        callbacks.unassign(lit);
        prop.values.unassign(lit.var());
        #[cfg(debug_assertions)]
        {
            // In debug builds we mark unassigned literals in `trail_index` so that on invalid
            // accesses we get a panic right away.
            prop.trail.trail_index[lit] = TrailIndex::UNASSIGNED;
        }
    }

    prop.trail.decisions.truncate(decision_level.0 as usize + 1);

    prop.trail.propagated = prop.trail.propagated.min(target_trail_len);
}
