//! Phase saving.

use crate::{
    lit::{Lit, Var},
    tracking::TracksVarCount,
    trail::BacktrackCallbacks,
    vec_map::VecMap,
};

/// Saves previously assigned phases to reuse them for decisions.
#[derive(Default)]
pub struct Phases {
    /// Saved phases.
    saved: VecMap<Var, bool>,
}

impl TracksVarCount for Phases {
    fn var_count(&self) -> usize {
        self.saved.len()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.saved.resize(var_count, false);
    }
}

impl BacktrackCallbacks for Phases {
    fn unassign(&mut self, lit: Lit) {
        // We update the saved phases when undoing assignments, as this is more convenient than
        // doing so during propagation. As we're only accessing the saved phases of unassigned
        // literals, this makes no logical difference to updating them when they are assigned.
        self.saved[lit] = lit.is_positive();
    }
}

impl Phases {
    /// Given a variable decision, this selects the phase to use for the decision.
    ///
    /// The returned literal has the argument as variable.
    pub fn decide_phase(&self, var: Var) -> Lit {
        Lit::from_var(var, self.saved[var])
    }
}
