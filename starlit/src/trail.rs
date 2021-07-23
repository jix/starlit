//! Stores a history of steps performed during the search to enable backtracking.

use crate::{
    clauses::{long::ClauseRef, AddedClause, Clauses},
    lit::{Lit, LitIdx, SignedLitIdx, Var},
    tracking::TracksVarCount,
};

// How I wish there was a `NotMaxU32` type or some other way to specify custom niche values...
/// Marker for variables that are unassigned.
const UNASSIGNED: SignedLitIdx = SignedLitIdx::MAX;

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
    pub fn lits<'a>(&'a self, clauses: &'a Clauses) -> &'a [Lit] {
        match self {
            Reason::Decision | Reason::Unit => &[],
            Reason::Binary(lit) => unsafe {
                // SAFETY `T` and `[T;1]` have the same size and alignment
                &*(lit as *const Lit as *const [Lit; 1])
            },
            Reason::Long(clause) => {
                // Unit propagation ensures that the falsified literals are contiguous.
                &clauses.long.lits(*clause)[1..]
            }
        }
    }
}

impl From<AddedClause> for Reason {
    fn from(added_clause: AddedClause) -> Self {
        match added_clause {
            AddedClause::Binary([_propagated, reason]) => Reason::Binary(reason),
            AddedClause::Long(clause) => Reason::Long(clause),
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
    pub decision_level: LitIdx,
    /// The propagating clause that assigned this literal.
    ///
    /// Used to represent the implication graph.
    pub reason: Reason,
}

/// Stores a history of steps performed during the search to enable backtracking.
///
/// This also contains the resulting variable assignment as well as the implication graph.
pub struct Trail {
    /// The state after performing all steps currently on the trail.
    pub assigned: PartialAssignment,

    /// The step on which a variable was assigned.
    trail_index: Vec<SignedLitIdx>,

    /// Sequence of performed steps.
    steps: Vec<Step>,

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
            assigned: PartialAssignment::default(),
            trail_index: vec![],
            steps: vec![],
            decisions: vec![0],
        }
    }
}

#[allow(clippy::len_without_is_empty)]
impl Trail {
    /// Adds a step that assigns a literal to the trail.
    pub fn assign(&mut self, step: Step) {
        self.trail_index[step.assigned_lit.index()] = self.steps.len() as _;
        debug_assert!(!self.assigned.is_assigned(step.assigned_lit.var()));
        self.assigned.assign(step.assigned_lit);
        self.steps.push(step);
    }

    /// Adds a step that assigns a literal as a new decision.
    pub fn assign_decision(&mut self, lit: Lit) {
        self.decisions.push(self.steps.len() as LitIdx);
        self.assign(Step {
            assigned_lit: lit,
            decision_level: self.decision_level(),
            reason: Reason::Decision,
        })
    }

    /// Returns the history of performed assignment steps.
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    /// Returns the step that assigned a given variable.
    ///
    /// With debug assertions enabled, this will panic if the variable is not assigned by a step on
    /// the trail. For release builds, calling this for an unassigned variable might panic or return
    /// bogus data. It is memory safe in either case.
    pub fn step_for_var(&self, var: Var) -> &Step {
        &self.steps[self.trail_index(var)]
    }

    /// Returns the index of the step that assigned a given variable.
    ///
    /// With debug assertions enabled, this will panic if the variable is not assigned by a step on
    /// the trail. For release builds, calling this for an unassigned variable might panic or return
    /// bogus data. It is memory safe in either case.
    pub fn trail_index(&self, var: Var) -> usize {
        let index = self.trail_index[var.index()];
        debug_assert_ne!(index, UNASSIGNED);
        debug_assert!(index >= 0);
        index as usize
    }

    /// Returns the trail index of the decision literal of a given decision level.
    ///
    /// Returns `0` if the passed decision level is `0`, which does not correspond to a decision,
    /// but indicates absence of a decision in the reason for a literal
    pub fn decision_trail_index(&self, decision_level: LitIdx) -> usize {
        self.decisions[decision_level as usize] as usize
    }

    /// Number of decisions made.
    pub fn decision_level(&self) -> LitIdx {
        (self.decisions.len() - 1) as LitIdx
    }

    /// Bactracks to a given decision level.
    ///
    /// This undoes all assignments of a higher decision level.
    ///
    /// Panics if the target decision level is the current decision level or higher.
    pub fn backtrack_to_level(
        &mut self,
        decision_level: LitIdx,
        callbacks: &mut impl BacktrackCallbacks,
    ) {
        tracing::trace!(decision_level, "backtrack");
        assert!(decision_level < self.decision_level());

        // Get the index corresponding to the lowest decision to undo
        let target_trail_len = self.decisions[decision_level as usize + 1] as usize;

        for step in self.steps.drain(target_trail_len..) {
            let lit = step.assigned_lit;
            // Undo the assignment
            callbacks.unassign(lit);
            self.assigned.unassign(lit.var());
            #[cfg(debug_assertions)]
            {
                // In debug builds we mark unassigned literals in `trail_index` so that on invalid
                // accesses we get a panic right away.
                self.trail_index[lit.index()] = UNASSIGNED;
            }
        }

        self.decisions.truncate(decision_level as usize + 1);
        callbacks.backtracked(self);
    }
}

/// Callbacks to synchronize state with backtracking on the trail.
pub trait BacktrackCallbacks {
    /// Called before undoing the assignment `lit`.
    fn unassign(&mut self, _lit: Lit) {}

    /// Called after backtracking finished with the resulting trail.
    fn backtracked(&mut self, _trail: &Trail) {}
}

impl BacktrackCallbacks for () {}

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
    /// Encoded partial assignment.
    ///
    /// Stored as one byte per variable. Each byte corresponds to an `Option<bool>`, but we encode
    /// it manually to get better codegen. We use `0`, `1`, `2` for `Some(false)`, `Some(true)`,
    /// `None` respectively.
    assigned: Vec<u8>,
}

impl PartialAssignment {
    /// Assigns `true` to the given literal.
    ///
    /// A variable can be assigned `false` by assigning `true` to the negated literal.
    #[inline(always)]
    pub fn assign(&mut self, lit: Lit) {
        self.assigned[lit.index()] = lit.is_positive() as u8
    }

    /// Removes any assigned value from a variable.
    #[inline(always)]
    pub fn unassign(&mut self, var: Var) {
        self.assigned[var.index()] = 2
    }

    /// Returns `true` if the literal is assigned `true`.
    #[inline(always)]
    pub fn is_true(&self, lit: Lit) -> bool {
        self.assigned[lit.index()] == lit.is_positive() as u8
    }

    /// Returns `true` if the literal is assigned `false`.
    #[inline(always)]
    pub fn is_false(&self, lit: Lit) -> bool {
        self.assigned[lit.index()] == lit.is_negative() as u8
    }

    /// Returns `true` if the literal is assigned.
    #[inline(always)]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.assigned[var.index()] != 2
    }
}

impl TracksVarCount for PartialAssignment {
    fn var_count(&self) -> usize {
        self.assigned.len()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.assigned.resize(var_count, 2);
    }
}
