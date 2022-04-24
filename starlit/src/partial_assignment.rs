//! A partial assignment to Boolean variabels.
use crate::{
    lit::{Lit, Var},
    tracking::Resize,
    util::vec_map::VecMap,
};

/// A partial assignment to Boolean variabels.
///
/// Each variable can be unassigned or assigned to a Boolean value.
#[derive(Default)]
pub struct PartialAssignment {
    /// Encoded partial assignment.
    ///
    /// Stored as one byte per variable. Each byte corresponds to an `Option<bool>`, but we encode
    /// it manually to get better codegen. We use `0`, `1`, `2` for `Some(true)`, `Some(false)`,
    /// `None` respectively, but xor it with the code of the positive literal corresponding to the
    /// variable. This makes the checks slightly faster.
    ///
    /// TODO It's not entirely clear to me why this would be the case, and I'm not sure it
    /// translates to other platforms or even other microarchitectures than those I've been
    /// benchmarking so far (AMD zen2).
    assigned: VecMap<Var, u8>,
}

impl PartialAssignment {
    /// Assigns `true` to the given literal.
    ///
    /// A variable can be assigned `false` by assigning `true` to the negated literal.
    #[inline(always)]
    pub fn assign(&mut self, lit: Lit) {
        self.assigned[lit] = lit.code() as u8
    }

    /// Removes any assigned value from a variable.
    #[inline(always)]
    pub fn unassign(&mut self, var: Var) {
        self.assigned[var] = (var.index() * 2) as u8 ^ 2
    }

    /// Returns `true` if the literal is assigned `true`.
    #[inline(always)]
    pub fn is_true(&self, lit: Lit) -> bool {
        self.assigned[lit] == lit.code() as u8
    }

    /// Returns `true` if the literal is assigned `false`.
    #[inline(always)]
    pub fn is_false(&self, lit: Lit) -> bool {
        self.assigned[lit] == lit.code() as u8 ^ 1
    }

    /// Returns `true` if the literal is assigned.
    #[inline(always)]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.assigned[var] != (var.index() * 2) as u8 ^ 2
    }
}

impl Resize for PartialAssignment {
    fn resize(&mut self, var_count: usize) {
        while self.assigned.len() < var_count {
            let index = self.assigned.len();
            self.assigned.push((index * 2) as u8 ^ 2);
        }
        self.assigned.truncate(var_count);
    }
}
