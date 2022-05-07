//! Solver components for propagation and backtracking.

use crate::{
    clause_arena::ClauseRefGcMap, context::Ctx, lit::Lit, partial_assignment::PartialAssignment,
    tracking::Resize,
};

use self::{
    binary::BinaryClauses,
    long::{ClauseRef, LongClauses, LongHeader},
    trail::{DecisionLevel, Reason, Step, Trail},
    watch::Watches,
};

pub mod binary;
pub mod long;
pub mod trail;
pub mod unit_prop;
pub mod watch;

/// Solver components for propagation and backtracking.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Prop {
    pub unsat: bool,
    pub values: PartialAssignment,
    pub binary: BinaryClauses,
    pub long: LongClauses,
    pub watches: Watches,
    pub trail: Trail,
}

impl Resize for Prop {
    fn resize(&mut self, var_count: usize) {
        self.values.resize(var_count);
        self.binary.resize(var_count);
        self.watches.resize(var_count);
        self.trail.resize(var_count);
    }
}

/// Propagation statistics.
#[derive(Default)]
pub struct PropStats {
    /// Total number of propagated assignments.
    pub propagations: u64,

    /// Current number of fixed variables.
    pub fixed_vars: usize,
}

/// Formula statistics.
#[derive(Default)]
pub struct FormulaStats {
    /// Current number of binary clauses.
    pub binary: u64,

    /// Current number of irredundant long clauses.
    pub irredundant: u64,

    /// Current number of redundant long clauses.
    pub redundant: u64,

    /// Current number of variables.
    pub vars: usize,
}

/// Reference to an added binary or long clause.
pub enum AddedClause {
    /// The empty clause.
    Empty,
    /// A unit clause.
    Unit(Lit),
    /// A reference to a binary clause, represented as the two contained literals.
    ///
    /// The order is the same as in the literals passed to [`add_clause_verbatim`].
    Binary([Lit; 2]),
    /// A reference to a long clause.
    Long(ClauseRef),
}

/// Add a clause to the formula without simplifying or reordering literals.
///
/// This can break solver invariants.
pub fn add_clause_verbatim(
    ctx: &mut Ctx,
    prop: &mut Prop,
    header: LongHeader,
    lits: &[Lit],
) -> AddedClause {
    match *lits {
        [] => {
            prop.unsat = true;
            AddedClause::Empty
        }
        [a] => {
            if prop.values.is_false(a) {
                prop.unsat = true;
                return AddedClause::Empty;
            }
            trail::assign(
                prop,
                Step {
                    assigned_lit: a,
                    decision_level: DecisionLevel::TOP,
                    reason: Reason::Unit,
                },
            );
            AddedClause::Unit(a)
        }
        [a, b] => {
            ctx.stats.formula.binary += 1;
            prop.binary.add_clause([a, b]);
            AddedClause::Binary([a, b])
        }
        [a, b, ..] => {
            if header.redundant() {
                ctx.stats.formula.redundant += 1;
            } else {
                ctx.stats.formula.irredundant += 1;
            }
            // TODO handle full clause arena
            let clause = prop.long.add_clause(header, lits).unwrap();
            prop.watches.watch_clause(clause, [a, b]);
            AddedClause::Long(clause)
        }
    }
}

/// Reference to a falsified clause.
#[derive(Debug)]
pub enum ConflictClause {
    /// The falsified clause is a binary clause.
    Binary([Lit; 2]),
    /// The falsified clause is a long clause.
    Long(ClauseRef),
}

impl ConflictClause {
    /// Returns the literals of the conflict clause.
    pub fn lits<'a>(&'a self, prop: &'a Prop) -> &'a [Lit] {
        match self {
            ConflictClause::Binary(lits) => lits,
            &ConflictClause::Long(clause) => prop.long.lits(clause),
        }
    }
}

/// Perfoms garbage collection when necessary.
pub fn collect_garbage(ctx: &mut Ctx, prop: &mut Prop) -> Option<ClauseRefGcMap> {
    prop.long
        .should_collect_garbage()
        .then(|| collect_garbage_now(ctx, prop))
}

/// Unconditionally performs garbage collection.
fn collect_garbage_now(ctx: &mut Ctx, prop: &mut Prop) -> ClauseRefGcMap {
    debug!(ctx, "garbage collection", prop.long.utilization());

    let gc_map = prop.long.collect_garbage();

    prop.trail.update_clause_references(&gc_map);

    prop.watches.update_clause_references(&gc_map);
    // TODO alternatively:
    // enable_watch_lists(prop, false);
    gc_map
}
