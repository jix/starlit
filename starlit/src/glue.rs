//! Glue computation.
use std::mem::replace;

use crate::{
    lit::Lit,
    trail::{DecisionLevel, Trail},
    vec_map::VecMap,
};

/// Computes the glue level of a clause.
///
/// The `tmp` argument must have a length of at least one more than the current decision level. It must
/// be initialized to all `false` and will reset to all `false` when this returns.
pub fn compute_glue(trail: &Trail, lits: &[Lit], tmp: &mut VecMap<DecisionLevel, bool>) -> usize {
    let mut glue = 0;
    for &lit in lits {
        if !replace(&mut tmp[trail.step_for_var(lit.var()).decision_level], true) {
            glue += 1;
        }
    }

    for &lit in lits {
        tmp[trail.step_for_var(lit.var()).decision_level] = false;
    }
    glue
}
