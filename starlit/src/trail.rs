//! Stores a history of steps performed during the search to enable backtracking.

use crate::{
    clauses::long::ClauseRef,
    lit::{Lit, LitIdx, SignedLitIdx, Var},
    tracking::TracksVarCount,
};

// How I wish there was a `NotMaxU32` type or some other way to specify custom niche values...
/// Marker for variables that are unassigned.
const UNASSIGNED: SignedLitIdx = SignedLitIdx::MAX;

/// The reason for an assignment, represents edges of the implication graph.
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

/// A step of the trail.
pub struct Step {
    /// The assigned literal.
    pub assigned_lit: Lit,
    /// The decision level of this step.
    ///
    /// The decision level of the `n`-th decision literal is `n`. For a propagated literal the
    /// decision level is the maximum decision level among the falsified literals in the propagating
    /// clause or zero if there are none.
    pub decision_level: LitIdx,
    /// The propagating clause that assigned this literal.
    ///
    /// Used to represent the implication graph.
    pub reason: Reason,
}

/// Stores a history of steps performed during the search to enable backtracking.
///
/// This also contains the resulting variable assignment as well as the implication graph.
#[derive(Default)]
pub struct Trail {
    /// The state after performing all steps currently on the trail.
    pub assigned: PartialAssignment,

    /// The step on which a variable was assigned.
    trail_index: Vec<SignedLitIdx>,

    /// Sequence of performed steps.
    steps: Vec<Step>,

    // TODO is this the right place?
    /// Size of the trail's prefix for which unit propagation was performed.
    pub propagated: usize,

    /// Number of decisions made.
    pub current_decision_level: LitIdx,
}

#[allow(clippy::len_without_is_empty)]
impl Trail {
    /// Adds a step that assigns a literal to the trail.
    pub fn assign(&mut self, step: Step) {
        self.trail_index[step.assigned_lit.index()] = self.steps.len() as _;
        self.assigned.assign(step.assigned_lit);
        self.steps.push(step);
    }

    /// Adds a step that assigns a literal as a new decision.
    pub fn assign_decision(&mut self, lit: Lit) {
        self.current_decision_level += 1;
        self.assign(Step {
            assigned_lit: lit,
            decision_level: self.current_decision_level,
            reason: Reason::Decision,
        })
    }

    /// Returns the history of performed assignment steps.
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    /// Returns the step that assigned a given variable.
    ///
    /// With debug assertions enabled, this will panic if the variable is not assigned. For release
    /// builds, calling this for an unassigned variable might panic or return bogus data. It is
    /// memory safe in either case.
    pub fn step_for_var(&self, var: Var) -> &Step {
        let index = self.trail_index[var.index()];
        debug_assert_ne!(index, UNASSIGNED);
        &self.steps[index as usize]
    }
}

impl TracksVarCount for Trail {
    fn var_count(&self) -> usize {
        self.assigned.var_count()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.assigned.set_var_count(var_count);

        self.trail_index.resize(var_count, UNASSIGNED)
    }
}

/// A partial assignment to Boolean variabels.
///
/// Each variable can be unassigned or assigned to a Boolean value.
#[derive(Default)]
pub struct PartialAssignment {
    assigned: Vec<Option<bool>>,
}

impl PartialAssignment {
    /// Assigns `true` to the given literal.
    ///
    /// A variable can be assigned `false` by assigning `true` to the negated literal.
    #[inline(always)]
    pub fn assign(&mut self, lit: Lit) {
        self.assigned[lit.index()] = Some(lit.is_positive())
    }

    /// Removes any assigned value from a variable.
    #[inline(always)]
    pub fn unassign(&mut self, var: Var) {
        self.assigned[var.index()] = None
    }

    /// Returns `true` if the literal is assigned `true`.
    #[inline(always)]
    pub fn is_true(&self, lit: Lit) -> bool {
        // TODO verify whether comparing two `Option<bool>` still generates branches and fix that
        // using a transmute hack
        self.assigned[lit.index()] == Some(lit.is_positive())
    }

    /// Returns `true` if the literal is assigned `false`.
    #[inline(always)]
    pub fn is_false(&self, lit: Lit) -> bool {
        // TODO verify whether comparing two `Option<bool>` still generates branches and fix that
        // using a transmute hack
        self.assigned[lit.index()] == Some(lit.is_negative())
    }

    /// Returns `true` if the literal is not assigned.
    #[inline(always)]
    pub fn is_unassigned(&self, lit: Lit) -> bool {
        // TODO verify whether comparing two `Option<bool>` still generates branches and fix that
        // using a transmute hack
        self.assigned[lit.index()] == None
    }
}

impl TracksVarCount for PartialAssignment {
    fn var_count(&self) -> usize {
        self.assigned.len()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.assigned.resize(var_count, None)
    }
}
