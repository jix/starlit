//! Learned clause minimization.
//!
//! This implements recursive learned clause minimization. It takes the 1-uip clause derived during
//! conflict analysis as input and removes all redundant literals. A literal is redundant if it is
//! implied by the remaining literals when considering the implications recored in the implication
//! graph.
//!
//! Searching the implication graph for such redundant literals is described by Sörensson and Biere
//! in ["Minimizing Learned Clauses"](https://doi.org/10.1007/978-3-642-02777-2_23). The idea to
//! cache both positive and negative results during the DFS to guarantee linear runtime is due to
//! Van Gelder ["Improved Conflict-Clause Minimization Leads to Improved Propositional Proof
//! Traces"](https://doi.org/10.1007/978-3-642-02777-2_15).
//!
//! Further useful observations and implementation techniques are presented by Fleury and Biere in
//! ["Efficient All-UIP Learned Clause Minimization"](https://doi.org/10.1007/978-3-030-80223-3_12).
//! That paper extends minimization in a way not yet implemented here, but also covers this
//! approach.
use std::mem::take;

use crate::{
    clauses::Clauses,
    lit::{Lit, LitIdx},
    trail::Trail,
};

/// Temporary data used during clause minimization.
#[derive(Default)]
pub struct MinimizeClause {
    /// Trail index of the first clause literal for each level.
    ///
    /// `LitIdx::MAX` if there is is no such literal, or if the level is yet to be processed.
    first_on_level: Vec<LitIdx>,
    /// Cache of whether a literal (by trail index) has a known redundancy wrt to the already
    /// processed clause literals.
    cache: Vec<Option<bool>>,
    /// Indices of values set in `cache`.
    to_clean: Vec<LitIdx>,
    /// Stack for the iterative DFS fallback.
    ///
    /// Always empty between calls, only here to cache the allocation.
    stack: Vec<StackItem<'static>>,
}

impl MinimizeClause {
    /// Removes redundant literals from a clause derived during conflict analysis.
    ///
    /// Returns the backtracking level that makes the clause propagating.
    pub fn minimize(&mut self, clause: &mut Vec<Lit>, trail: &Trail, clauses: &Clauses) -> LitIdx {
        // Resize temporary buffers if necessary
        if self.first_on_level.len() <= trail.decision_level() as usize {
            self.first_on_level
                .resize(trail.decision_level() as usize + 1, LitIdx::MAX);
        }

        if self.cache.len() <= trail.steps().len() {
            self.cache.resize(trail.steps().len(), None);
        }

        // Sort the clause literals chronologically
        clause.sort_unstable_by_key(|lit| trail.trail_index(lit.var()));

        let propagated = clause.pop().unwrap(); // Don't minimize the propagated literal

        clause.retain(|&lit| {
            let index = trail.trail_index(lit.var());
            let level = trail.steps()[index].decision_level as usize;
            let retain = if self.first_on_level[level] as usize > index {
                // The first literal of each decision level in the clause cannot be redundant
                self.first_on_level[level] = index as LitIdx;
                true
            } else {
                !self.is_redundant_literal_index_rec(index, trail, clauses, 0)
            };

            // After retaining a literal, it is redundant wrt to the retained literals even if it
            // wasn't before.
            self.cache[index] = Some(true);
            self.to_clean.push(index as LitIdx);
            retain
        });

        clause.push(propagated);

        // Clean up temporary buffers for the next minimization
        for index in self.to_clean.drain(..) {
            self.cache[index as usize] = None;
        }

        for &lit in clause.iter() {
            let index = trail.trail_index(lit.var());
            let level = trail.steps()[index].decision_level as usize;

            self.first_on_level[level] = LitIdx::MAX;
        }

        // Reverse the clause so the propagated literal is first and a literal of the backtrack
        // level is second.
        clause.reverse();
        trail.step_for_var(clause[1].var()).decision_level
    }

    /// Returns a cached (or trivial) result for `is_redundant_literal_index_rec`
    ///
    /// Trivial cases are top-level assignments, which are always redundant, and assignments that
    /// precede all clause literals on the same level, which are never redundant.
    fn is_redundant_literal_index_cached(&mut self, index: usize, trail: &Trail) -> Option<bool> {
        let step = &trail.steps()[index];
        let level = step.decision_level as usize;
        if level == 0 {
            // Top level assignments are always implied
            Some(true)
        } else if self.first_on_level[level] as usize > index {
            // Assignments before the first clause literal on the same level cannot be implied by
            // clause literals. This includes literals on levels with no clause literals.

            // This combines all three "Poison Criteria", as well as the decision check of ["Efficient All-UIP Learned Clause
            // Minimization"](https://doi.org/10.1007/978-3-030-80223-3_12) into a single check.
            Some(false)
        } else {
            self.cache[index]
        }
    }

    /// Performs a depth-first search with lookahead to check whether the assignment at trail
    /// `index` is implied by (other) literals of the clause.
    ///
    /// This caches positive as well as negative results to ensure an overall linear runtime.
    fn is_redundant_literal_index_rec(
        &mut self,
        index: usize,
        trail: &Trail,
        clauses: &Clauses,
        depth: usize,
    ) -> bool {
        // Check for a cached or trivial result
        if let Some(cached) = self.is_redundant_literal_index_cached(index, trail) {
            return cached;
        }

        let reason_lits = trail.steps()[index].reason.lits(clauses);

        // We perform a lookahead using cached/trivial values of depth 1 and only recurse if that is
        // not enough to determine the redundancy of the literal at the queried `index`.
        let mut all_true = true;
        for &reason_lit in reason_lits {
            let reason_index = trail.trail_index(reason_lit.var());
            match self.is_redundant_literal_index_cached(reason_index, trail) {
                Some(false) => {
                    self.cache[index] = Some(false);
                    self.to_clean.push(index as LitIdx);
                    return false;
                }
                Some(true) => (),
                None => all_true = false,
            }
        }

        if !all_true {
            // When there were reason literals of unknown redundancy, recurse

            if depth > 20 {
                // To avoid stack overflows, at a certain depth, we switch to the slightly slower
                // iterative version.
                return self.is_redundant_literal_index_iter(index, reason_lits, trail, clauses);
            }

            for &reason_lit in reason_lits {
                let reason_index = trail.trail_index(reason_lit.var());
                if !self.is_redundant_literal_index_rec(reason_index, trail, clauses, depth + 1) {
                    self.cache[index] = Some(false);
                    self.to_clean.push(index as LitIdx);
                    return false;
                }
            }
        }

        self.cache[index] = Some(true);
        self.to_clean.push(index as LitIdx);
        true
    }

    /// An iterative version of `Self::is_redundant_literal_index_rec`.
    #[cold] // Only used as fallback
    fn is_redundant_literal_index_iter(
        &mut self,
        index: usize,
        reason_lits: &[Lit],
        trail: &Trail,
        clauses: &Clauses,
    ) -> bool {
        // This goes through the exact same steps as the recursive version, except for skipping the
        // initial checks for the outermost call (see where it is invoked from the recursive
        // version) and for that it manually manages a stack instead of using the call stack. See
        // the recursive version for comments.

        self.stack.clear(); // no-op to make this safe unconditionally
        let mut stack: Vec<StackItem> = unsafe {
            // SAFETY stack is empty and we only transmute the lifetime
            std::mem::transmute(take(&mut self.stack))
        };

        macro_rules! return_false {
            () => {
                for item in stack.drain(..) {
                    self.cache[item.index] = Some(false);
                    self.to_clean.push(item.index as LitIdx);
                }

                self.stack = unsafe {
                    // SAFETY stack is empty and we only transmute the lifetime
                    std::mem::transmute(stack)
                };

                return false;
            };
        }

        // Keeping the top of the stack in a local variable that is updated when pushing/popping is
        // faster than popping and pushing on every iteration
        let mut top = StackItem { index, reason_lits };

        loop {
            while let Some((&lit, rest)) = top.reason_lits.split_first() {
                top.reason_lits = rest;

                let index = trail.trail_index(lit.var());

                match self.is_redundant_literal_index_cached(index, trail) {
                    Some(true) => continue,

                    Some(false) => {
                        self.cache[top.index] = Some(false);
                        self.to_clean.push(top.index as LitIdx);
                        return_false!();
                    }
                    None => {
                        let reason_lits = trail.steps()[index].reason.lits(clauses);
                        let mut all_true = true;
                        for &reason_lit in reason_lits {
                            let reason_index = trail.trail_index(reason_lit.var());
                            match self.is_redundant_literal_index_cached(reason_index, trail) {
                                Some(false) => {
                                    self.cache[index] = Some(false);
                                    self.to_clean.push(index as LitIdx);
                                    self.cache[top.index] = Some(false);
                                    self.to_clean.push(top.index as LitIdx);
                                    return_false!();
                                }
                                Some(true) => (),
                                None => all_true = false,
                            }
                        }
                        if all_true {
                            self.cache[index] = Some(true);
                            self.to_clean.push(index as LitIdx);
                        } else {
                            stack.push(std::mem::replace(
                                &mut top,
                                StackItem { index, reason_lits },
                            ));
                        }
                    }
                }
            }
            self.cache[top.index] = Some(true);
            self.to_clean.push(top.index as LitIdx);
            if let Some(new_top) = stack.pop() {
                top = new_top;
            } else {
                break;
            }
        }

        self.stack = unsafe {
            // SAFETY stack is empty and we only transmute the lifetime
            std::mem::transmute(stack)
        };

        true
    }
}

/// Stack item for the iterative DFS fallback.
#[derive(Debug)]
struct StackItem<'a> {
    /// Trail index of the current literal.
    index: usize,
    /// Pending (not yet visited) reason literals for the current literal.
    reason_lits: &'a [Lit],
}
