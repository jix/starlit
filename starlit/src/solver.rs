//! SAT solver entrypoint.
use crate::{
    context::Ctx,
    lit::Lit,
    log::HasLogger,
    prop::{add_clause_verbatim, long::LongHeader},
    report::report,
    state::{schedule_search_step, State},
    tracking::Resize,
};

/// A complete SAT solver.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Solver {
    pub ctx: Ctx,
    pub state: State,
}

impl Solver {
    /// Adds a clause to the current formula.
    pub fn add_clause(&mut self, clause: &[Lit]) {
        // TODO this is just a temporary hack

        let var_count = clause
            .iter()
            .map(|lit| lit.index() + 1)
            .max()
            .unwrap_or_default();

        if self.ctx.stats.formula.vars < var_count {
            self.ctx.stats.formula.vars = var_count;
            self.state.resize(var_count);
        }

        add_clause_verbatim(
            &mut self.ctx,
            &mut self.state.search.prop,
            LongHeader::new_input_clause(),
            clause,
        );
    }

    /// Determines whether the current formula is satisfiable.
    pub fn solve(&mut self) -> bool {
        loop {
            if let Some(result) = schedule_search_step(&mut self.ctx, &mut self.state) {
                report(&mut self.ctx);
                return result;
            }
        }
    }

    /// Returns the value assigned to a literal.
    pub fn value(&self, lit: Lit) -> Option<bool> {
        if lit.index() < self.ctx.stats.formula.vars {
            self.state.search.prop.values.value(lit)
        } else {
            None
        }
    }
}

impl HasLogger for Solver {
    #[inline(always)]
    fn logger(&self) -> &crate::log::Logger {
        self.ctx.logger()
    }
}
