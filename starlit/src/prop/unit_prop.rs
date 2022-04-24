//! Unit propagation for CNF clauses.
//!
//! This implements watch list based unit propagation for CNF clauses. Unit propagation is the
//! process of repeatedly extending the current partial assignment by all literals propagated by
//! clauses that are unit under the current assignment until none are left or until a clause is in
//! conflict.
use crate::{lit::Lit, util::mut_scan::MutScan};

use super::{
    trail::{self, Reason, Step},
    watch::enable_watch_lists,
    ConflictClause, Prop,
};

/// Performs unit propagation.
pub fn propagate(prop: &mut Prop) -> Result<(), ConflictClause> {
    enable_watch_lists(prop, true);

    while let Some(lit) = prop.trail.next_unpropagated_lit() {
        propagate_literal(prop, lit)?;
        prop.trail.advance_propagated();
    }

    Ok(())
}

/// Finds clauses that become unit or falsified when `lit` is assigned true.
#[inline(always)]
pub fn propagate_literal(prop: &mut Prop, lit: Lit) -> Result<(), ConflictClause> {
    propagate_binary_clauses(prop, lit)?;
    propagate_long_clauses(prop, lit)
}

/// Finds binary clauses that become unit or falsified when `lit` is assigned true.
#[inline(always)]
fn propagate_binary_clauses(prop: &mut Prop, lit: Lit) -> Result<(), ConflictClause> {
    // `lit` is assigned `true`, so clauses containing `!lit` could become unit or falsified.
    let clause_lit = !lit;

    for &other_lit in prop.binary.containing(clause_lit) {
        // If the clause is already satisfied, there is nothing to do
        if !prop.values.is_true(other_lit) {
            // If the other literal is also false, the clause is in conflict
            if prop.values.is_false(other_lit) {
                return Err(ConflictClause::Binary([clause_lit, other_lit]));
            } else {
                // Otherwise the clause is unit and non-satisfied, so we propagate its other
                // literal
                let decision_level = prop.trail.decision_level();
                trail::assign_raw(
                    &mut prop.values,
                    &mut prop.trail,
                    Step {
                        assigned_lit: other_lit,
                        decision_level,
                        reason: Reason::Binary(clause_lit),
                    },
                );
            }
        }
    }

    Ok(())
}

/// Finds long clauses that become unit or falsified when `lit` is assigned true.
#[inline(always)]
fn propagate_long_clauses(prop: &mut Prop, lit: Lit) -> Result<(), ConflictClause> {
    // `lit` is assigned `true`, so clauses containing `!lit` could become unit or falsified.
    let watched_lit = !lit;

    let mut watches = prop.watches.take(watched_lit);

    let mut scan = MutScan::new(&mut watches);

    let mut result = Ok(());

    'outer: while let Some(mut watch) = scan.next() {
        // We need to maintain the invariant that, unless we detected a conflict, for each
        // clause there either a) are two watched non-false literals, or b) there is a true
        // literal. All this in such a way that undoing assignments during backtracking will
        // maintain this invariant without moving any watches.
        //
        // If the blocked literal or the other watched literal are true, b) holds and we are
        // done.
        //
        // Otherwise we search for a non-false literal among the non-watched literals.
        //
        // If we find an unassigned literal we move our watch to it. For the case where the
        // other watched literal is non-false, this restores a). If the other watched literal is
        // false, this is not yet the case, but this means that the other watched literal is
        // still pending on the propagation queue and we will restore the invariant when we get
        // around to process it. Thus, in both cases we are done.
        //
        // If we find a true literal b) also holds, so we would not have to do anything. If we
        // don't do anything at all, though, the next time the watched literal gets re-assigned
        // the same value, we would again search the non-watched literals. We can avoid this in
        // two ways: 1) we set the blocking literal of our watch to the found literal or 2) we
        // move the watch to the found literal, the same way as we do when we find an unassigned
        // literal.
        //
        // As 1) only touches memory that we already accessed, this is what we use.
        //
        // Finally, if there is no other non-false literal, all but the other watched literal
        // must be false. If the other watched literal is also false, we have a conflict.
        // Otherwise this clause asserts the other watched literal, enqueuing a new propagation
        // and turning it from unassigned to true. After that b) holds again.

        if prop.values.is_true(watch.blocking_lit) {
            watch.keep();
            continue; // Clause already satisfied by `blocking_lit`.
        }
        let (clause_header, clause_lits) = prop.long.header_and_lits_mut(watch.clause);
        if clause_lits.len() < 2 {
            // This only happens when the clause was deleted but not yet collected.
            watch.remove(); // No need to continue watching a deleted clause.
            continue;
        }

        // The two watched literals are always kept in the first two slots
        let other_watched_lit = watched_lit.select_other(clause_lits[0], clause_lits[1]);

        if prop.values.is_true(other_watched_lit) {
            // Clause is already satisfied by the other watched literal, so we replace the
            // blocking literal to increase the chance of detecting this early the next time we
            // scan this watch list.
            watch.blocking_lit = other_watched_lit;

            watch.keep();
            continue;
        }

        // When searching for a non-false non-watched literal, we continue where the last such
        // search for this clause stopped. This avoids accidentally quadratic behaviour, in case
        // a large prefix of the clause is falsified early on the trail.
        //
        // See also ["Optimal Implementation of Watched Literals and More General
        // Techniques"](https://doi.org/10.1613/jair.4016)
        let mut search_pos = clause_header.search_pos();

        let search_len = clause_lits.len() - 2;

        for _ in 0..search_len {
            let search_lit = clause_lits[2 + search_pos];
            if !prop.values.is_false(search_lit) {
                // We found a non-false literal!
                if prop.values.is_true(search_lit) {
                    // It is true, no need to move the watch, but update the blocking literal
                    watch.blocking_lit = search_lit;
                    clause_header.set_search_pos(search_pos);

                    watch.keep();
                } else {
                    // It is unassigned, move our watch
                    watch.blocking_lit = other_watched_lit;
                    prop.watches.push_watch(search_lit, watch.remove());
                    clause_header.set_search_pos(search_pos);
                    // Move the newly watched literal to the beginning of the clause
                    clause_lits[0] = search_lit; // Newly watched
                    clause_lits[1] = other_watched_lit;
                    clause_lits[2 + search_pos] = watched_lit; // Not watched anymore
                }
                continue 'outer;
            }
            search_pos += 1;
            if search_pos == search_len {
                // TODO make this branchfree? benchmark!
                search_pos = 0;
            }
        }
        clause_header.set_search_pos(search_pos);

        // All non-watched literals, as well as `watched_lit` are false

        if prop.values.is_false(other_watched_lit) {
            // All literals are false, i.e. we have a conflict
            result = Err(ConflictClause::Long(watch.clause));

            watch.keep();
            break;
        } else {
            // This clause asserts `other_watched_lit`.

            // Make sure the asserted literal is the first, so the asserting literals form a
            // contiguous slice.
            clause_lits[0] = other_watched_lit;
            clause_lits[1] = watched_lit;

            let decision_level = prop.trail.decision_level();

            trail::assign_raw(
                &mut prop.values,
                &mut prop.trail,
                Step {
                    assigned_lit: other_watched_lit,
                    decision_level,
                    reason: Reason::Long(watch.clause),
                },
            );

            watch.keep();
        }
    }

    drop(scan);

    prop.watches.restore(!lit, watches);

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::tracking::Resize;

    use crate::prop::{add_clause_verbatim, long::LongHeader, trail::assign_decision, Prop};

    macro_rules! clause {
        ($($lit:literal),* $(,)?) => {{
            [$(Lit::from_dimacs($lit)),*]
        }};
    }

    macro_rules! clauses {
        ($var_count:literal vars $($($lit:literal),+);* $(;)?) => {{
            let mut prop = Prop::default();
            prop.resize($var_count);
            $(
                add_clause_verbatim(
                    &mut prop,
                    LongHeader::new_input_clause(),
                    &[$(Lit::from_dimacs($lit)),*],
                );
            )*
            prop
        }};
    }

    macro_rules! assign_unit {
        ($prop:ident, $lit:literal) => {
            assign_decision(&mut $prop, Lit::from_dimacs($lit));
        };
    }

    macro_rules! assert_assigned {
        ($prop:ident, $($lit:literal),*) => {
            let mut assigned = $prop
                .trail
                .steps()
                .iter()
                .map(|step| step.assigned_lit)
                .collect::<Vec<_>>();
            let mut expected = vec![$(Lit::from_dimacs($lit)),*];
            assigned.sort_unstable();
            expected.sort_unstable();
            assert_eq!(assigned, expected);
        };
    }

    #[test]
    fn simple_prop() {
        let mut prop = clauses![4 vars
            -1, 2;
            -2, 3;
            -2, -3, -4;
        ];

        assign_unit!(prop, 1);

        assert!(propagate(&mut prop).is_ok());
        assert_assigned!(prop, 1, 2, 3, -4);
    }

    #[test]
    fn two_step_prop() {
        let mut prop = clauses![7 vars
            -1, 2;
            -2, 3;
            -2, -3, -4, -5, -6, -7;
            -4, 5;
            -5, 6;
        ];

        assign_unit!(prop, 1);
        assert!(propagate(&mut prop).is_ok());
        assert_assigned!(prop, 1, 2, 3);

        assign_unit!(prop, 4);
        assert!(propagate(&mut prop).is_ok());
        assert_assigned!(prop, 1, 2, 3, 4, 5, 6, -7);
    }

    #[test]
    fn binary_conflict() {
        let mut prop = clauses![3 vars
            -1, 2;
            -1, 3;
            -2, -3;
        ];

        assign_unit!(prop, 1);
        match propagate(&mut prop) {
            Err(ConflictClause::Binary(mut binary)) => {
                binary.sort();
                assert_eq!(binary, clause![-2, -3]);
            }
            _ => panic!("expected binary conflict"),
        }
    }

    #[test]
    fn long_conflict() {
        let mut prop = clauses![8 vars
            -1, 2;
            -1, 3;
            -2, -3, 4;
            -3, 5;
            -4, -2, -3, -5, -1, -7, -8;
            -6, 7;
            -6, 8;
        ];

        assign_unit!(prop, 1);
        assert!(propagate(&mut prop).is_ok());

        assign_unit!(prop, 6);
        match propagate(&mut prop) {
            Err(ConflictClause::Long(clause)) => {
                let mut conflict_lits = prop.long.lits(clause).to_vec();
                conflict_lits.sort();
                assert_eq!(conflict_lits, clause![-1, -2, -3, -4, -5, -7, -8]);
            }
            _ => panic!("expected long conflict"),
        }
    }
}
