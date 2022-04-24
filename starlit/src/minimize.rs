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
    lit::Lit,
    prop::{
        trail::{DecisionLevel, Trail, TrailIndex},
        Prop,
    },
    util::vec_map::VecMap,
};

/// Temporary data used during clause minimization.
#[derive(Default)]
pub struct MinimizeClause {
    /// Trail index of the first clause literal for each level.
    ///
    /// `LitIdx::MAX` if there is is no such literal, or if the level is yet to be processed.
    first_on_level: VecMap<DecisionLevel, TrailIndex>,
    /// Cache of whether a literal (by trail index) has a known redundancy wrt to the already
    /// processed clause literals.
    cache: VecMap<TrailIndex, Option<bool>>,
    /// Indices of values set in `cache`.
    to_clean: Vec<TrailIndex>,
    /// Stack for the iterative DFS fallback.
    ///
    /// Always empty between calls, only here to cache the allocation.
    stack: Vec<StackItem<'static>>,
}

/// Removes redundant literals from a clause derived during conflict analysis.
///
/// Returns the backtracking level that makes the clause propagating.
pub fn minimize(
    minimize: &mut MinimizeClause,
    clause: &mut Vec<Lit>,
    prop: &Prop,
) -> DecisionLevel {
    // Resize temporary buffers if necessary
    if minimize.first_on_level.len() <= prop.trail.decision_level().0 as usize {
        minimize.first_on_level.resize(
            prop.trail.decision_level().0 as usize + 1,
            TrailIndex::UNASSIGNED,
        );
    }

    minimize.first_on_level[DecisionLevel::TOP] = TrailIndex(0);

    if minimize.cache.len() <= prop.trail.steps().len() {
        minimize.cache.resize(prop.trail.steps().len(), None);
    }

    // Sort the clause literals chronologically
    clause.sort_unstable_by_key(|lit| prop.trail.trail_index(lit.var()));

    let propagated = clause.pop().unwrap(); // Don't minimize the propagated literal

    clause.retain(|&lit| {
        let index = prop.trail.trail_index(lit.var());
        let level = prop.trail.steps()[index].decision_level;
        let retain = if minimize.first_on_level[level] > index {
            // The first literal of each decision level in the clause cannot be redundant
            minimize.first_on_level[level] = index;
            true
        } else {
            !literal_index_is_redundant_rec_uncached(minimize, index, prop, 0)
        };

        // After retaining a literal, it is redundant wrt to the retained literals even if it
        // wasn't before.
        minimize.cache[index] = Some(true);
        minimize.to_clean.push(index);
        retain
    });

    clause.push(propagated);

    // Clean up temporary buffers for the next minimization
    for index in minimize.to_clean.drain(..) {
        minimize.cache[index] = None;
    }

    for &lit in clause.iter() {
        let index = prop.trail.trail_index(lit.var());
        let level = prop.trail.steps()[index].decision_level;

        minimize.first_on_level[level] = TrailIndex::UNASSIGNED;
    }

    // Reverse the clause so the propagated literal is first and a literal of the backtrack
    // level is second.
    clause.reverse();
    prop.trail.step_for_var(clause[1].var()).decision_level
}

/// Returns a cached (or trivial) result for `is_redundant_literal_index_rec`
///
/// Trivial cases are top-level assignments, which are always redundant, and assignments that
/// precede all clause literals on the same level, which are never redundant.
fn literal_index_is_redundant_cached(
    minimize: &mut MinimizeClause,
    index: TrailIndex,
    trail: &Trail,
) -> Option<bool> {
    minimize.cache[index].or_else(|| {
        let step = &trail.steps()[index];
        let level = step.decision_level;
        if minimize.first_on_level[level] > index {
            // Assignments before the first clause literal on the same level cannot be implied
            // by clause literals. This includes literals on levels with no clause literals.

            // This combines all three "Poison Criteria", as well as the decision check of
            // ["Efficient All-UIP Learned Clause
            // Minimization"](https://doi.org/10.1007/978-3-030-80223-3_12) into a single check.
            Some(false)
        } else if level == DecisionLevel::TOP {
            Some(true)
        } else {
            None
        }
    })
}

/// Performs a depth-first search with lookahead to check whether the assignment at trail
/// `index` is implied by (other) literals of the clause.
///
/// This caches positive as well as negative results to ensure an overall linear runtime.
fn literal_index_is_redundant_rec(
    minimize: &mut MinimizeClause,
    index: TrailIndex,
    prop: &Prop,
    depth: usize,
) -> bool {
    // Check for a cached or trivial result
    if let Some(cached) = literal_index_is_redundant_cached(minimize, index, &prop.trail) {
        return cached;
    }
    literal_index_is_redundant_rec_uncached(minimize, index, prop, depth)
}

/// The same as `is_redundant_literal_index_rec`, but does not perform a cache lookup for the
/// outermost call.
fn literal_index_is_redundant_rec_uncached(
    minimize: &mut MinimizeClause,
    index: TrailIndex,
    prop: &Prop,
    depth: usize,
) -> bool {
    let reason_lits = prop.trail.steps()[index].reason.lits(prop);

    // We perform a lookahead using cached/trivial values of depth 1 and only recurse if that is
    // not enough to determine the redundancy of the literal at the queried `index`.
    let mut all_true = true;
    for &reason_lit in reason_lits {
        let reason_index = prop.trail.trail_index(reason_lit.var());
        match literal_index_is_redundant_cached(minimize, reason_index, &prop.trail) {
            Some(false) => {
                minimize.cache[index] = Some(false);
                minimize.to_clean.push(index);
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
            return literal_index_is_redundant_iter(minimize, index, reason_lits, prop);
        }

        for &reason_lit in reason_lits {
            let reason_index = prop.trail.trail_index(reason_lit.var());
            if !literal_index_is_redundant_rec(minimize, reason_index, prop, depth + 1) {
                minimize.cache[index] = Some(false);
                minimize.to_clean.push(index);
                return false;
            }
        }
    }

    minimize.cache[index] = Some(true);
    minimize.to_clean.push(index);
    true
}

/// An iterative version of `Self::is_redundant_literal_index_rec`.
#[cold] // Only used as fallback
fn literal_index_is_redundant_iter(
    minimize: &mut MinimizeClause,
    index: TrailIndex,
    reason_lits: &[Lit],
    prop: &Prop,
) -> bool {
    // This goes through the exact same steps as the recursive version, except for skipping the
    // initial checks for the outermost call (see where it is invoked from the recursive
    // version) and for that it manually manages a stack instead of using the call stack. See
    // the recursive version for comments.

    minimize.stack.clear(); // no-op to make this safe unconditionally
    let mut stack: Vec<StackItem> = unsafe {
        // SAFETY stack is empty and we only transmute the lifetime
        std::mem::transmute(take(&mut minimize.stack))
    };

    macro_rules! return_false {
        () => {
            for item in stack.drain(..) {
                minimize.cache[item.index] = Some(false);
                minimize.to_clean.push(item.index);
            }

            minimize.stack = unsafe {
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

            let index = prop.trail.trail_index(lit.var());

            match literal_index_is_redundant_cached(minimize, index, &prop.trail) {
                Some(true) => continue,

                Some(false) => {
                    minimize.cache[top.index] = Some(false);
                    minimize.to_clean.push(top.index);
                    return_false!();
                }
                None => {
                    let reason_lits = prop.trail.steps()[index].reason.lits(prop);
                    let mut all_true = true;
                    for &reason_lit in reason_lits {
                        let reason_index = prop.trail.trail_index(reason_lit.var());
                        match literal_index_is_redundant_cached(minimize, reason_index, &prop.trail)
                        {
                            Some(false) => {
                                minimize.cache[index] = Some(false);
                                minimize.to_clean.push(index);
                                minimize.cache[top.index] = Some(false);
                                minimize.to_clean.push(top.index);
                                return_false!();
                            }
                            Some(true) => (),
                            None => all_true = false,
                        }
                    }
                    if all_true {
                        minimize.cache[index] = Some(true);
                        minimize.to_clean.push(index);
                    } else {
                        stack.push(std::mem::replace(
                            &mut top,
                            StackItem { index, reason_lits },
                        ));
                    }
                }
            }
        }
        minimize.cache[top.index] = Some(true);
        minimize.to_clean.push(top.index);
        if let Some(new_top) = stack.pop() {
            top = new_top;
        } else {
            break;
        }
    }

    minimize.stack = unsafe {
        // SAFETY stack is empty and we only transmute the lifetime
        std::mem::transmute(stack)
    };

    true
}

/// Stack item for the iterative DFS fallback.
#[derive(Debug)]
struct StackItem<'a> {
    /// Trail index of the current literal.
    index: TrailIndex,
    /// Pending (not yet visited) reason literals for the current literal.
    reason_lits: &'a [Lit],
}
