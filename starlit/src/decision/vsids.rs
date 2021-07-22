//! VSIDS decision heuristic.
//!
//! This implements the (exponential) Variable State Independent Decaying Sum decision heuristic.
//! Conceptionally this maintains a score for each variable. For every conflict, the scores of a
//! small subset of variables are incremented by one, called bumping, followed by multiplying the
//! scores of all variables by a positive decay factor smaller than 1.
//!
//! When the sovler makes a heuristic decision, the unassigned variable with the highest score is
//! selected.
//!
//! This was introduced (with per literal scores and multiple conflicts inbetween decay steps) in
//! the solver Chaff (see ["Chaff: Engineering an Efficient SAT
//! Solver"](https://doi.org/10.1145/378239.379017)).
//!
//! To get an efficient implementation we need to avoid updating every variable's score every
//! conflict. As we are only interested in the relative order of scores and not their absolute
//! value, we can avoid this by rescaling. Instead of adding the constant 1 when bumping a score, we
//! add a variable `increment`, initially set to 1. Then instead of multiplying all scores by
//! `decay`, we divide `increment` by `decay`. The ratio of any two scores is the same as above.
//!
//! A small caveat is that eventually variable scores and/or `decay` will exceed the range
//! representable by floating point numbers. This needs to be detected, in which case all scores and
//! `decay` are multiplied by a small constant to keep them in range.
//!
//! This implementation strategy is due to MiniSat and explained in ["An Extensible
//! SAT-solver"](https://doi.org/10.1007/978-3-540-24605-3_37).
//!
//! Initially, in Chaff and the first version of MiniSat, the set of bumped variables consisted of
//! the variables in the learned clause. Newer versions of MiniSat and most (all?) recent solvers
//! bump all conflict side variables instead (i.e. variables in the learned clause as well as
//! variables resolved on during learning). This seems to have been introduced by the solver BerkMin
//! (see ["BerkMin: A fast and robust SAT-solver"](https://doi.org/10.1016/j.dam.2006.10.007)), but
//! many more recent descriptions of VSIDS describe this variant without explicitly pointing out
//! this change from the original approach.
//!
//! Finding the unassigned variable with the highest score is implemented using a heap data
//! structure. The heap always constains a superset of the unassigned variables. Assigned variables
//! are removed lazily, i.e. an assigned variable is removed when the highest score turns out to be
//! already assigned, but unassigned variables are added eagerly, i.e. as soon as they are
//! unassigned.
use crate::{
    heap::MaxHeap,
    lit::Var,
    tracking::TracksVarCount,
    trail::{BacktrackCallbacks, PartialAssignment},
};

const RESCALE_LIMIT: f32 = std::f32::MAX / 16.0;
const RESCALE_FACTOR: f32 = 1.0 / RESCALE_LIMIT;
const INVERSE_DECAY: f32 = 1.0 / 0.95; // TODO make configurable / dynamic

/// The VSIDS decision heuristic.
pub struct Vsids {
    /// Variable activity.
    ///
    /// Actually stored as `f32`s, but always positive so we can compare them as `u32`s.
    activity: MaxHeap<u32>,
    /// Amount to increase the activity of a bumped variable.
    increment: f32,
}

impl Default for Vsids {
    fn default() -> Self {
        Self {
            activity: Default::default(),
            increment: 1.0,
        }
    }
}

impl BacktrackCallbacks for Vsids {
    fn unassign(&mut self, lit: crate::lit::Lit) {
        self.activity.enqueue(lit.index())
    }
}

impl TracksVarCount for Vsids {
    fn var_count(&self) -> usize {
        self.activity.len()
    }

    fn set_var_count(&mut self, var_count: usize) {
        let old_var_count = self.var_count();
        self.activity.resize(var_count, 0);
        for index in old_var_count..var_count {
            self.activity.enqueue(index);
        }
    }
}

impl Vsids {
    /// Increments a variable's score.
    pub fn bump_var(&mut self, var: Var) {
        let mut rescale = false;

        let increment = self.increment;

        self.activity.increase(var.index(), |activity_bits| {
            let mut activity = f32::from_bits(*activity_bits);

            activity += increment;

            if activity > RESCALE_LIMIT {
                rescale = true;
            }

            *activity_bits = activity.to_bits();
        });

        if rescale {
            self.rescale();
        }
    }

    /// Decays all variable scores.
    pub fn decay(&mut self) {
        self.increment *= INVERSE_DECAY;
        if self.increment > RESCALE_LIMIT {
            self.rescale();
        }
    }

    /// Returns the variable with the highest score and mark at is assigned.
    pub fn pop_decision_var(&mut self, assignment: &PartialAssignment) -> Option<Var> {
        // Assigned variables are not eagerly removed from the heap, so we pop variables until we
        // find an unassigned variable.
        while let Some(index) = self.activity.pop_max() {
            let var = Var::from_index(index);
            if !assignment.is_assigned(var) {
                return Some(var);
            }
        }
        None
    }

    /// Rescales all scores and the bump increment.
    ///
    /// Used to keep both in range.
    fn rescale(&mut self) {
        self.activity.apply_monotone(|activity_bits| {
            let mut activity = f32::from_bits(*activity_bits);

            activity *= RESCALE_FACTOR;

            *activity_bits = activity.to_bits();
        });

        self.increment *= RESCALE_FACTOR;
    }
}
