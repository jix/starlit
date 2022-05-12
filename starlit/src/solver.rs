//! SAT solver entrypoint.
use crate::{
    context::Ctx,
    lit::Lit,
    log::HasLogger,
    proof::Proof,
    prop::{add_clause_verbatim, long::LongHeader},
    report::report,
    state::{schedule_search_step, State},
    tracking::Resize,
};

/// A complete SAT solver.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Solver<'a> {
    pub ctx: Ctx<'a>,
    pub state: State,
}

impl<'a> Solver<'a> {
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

    /// Starts writing a proof using the provider writer.
    pub fn write_proof(&mut self, proof: Box<dyn Proof + 'a>) {
        self.ctx.proof = Some(proof)
    }

    /// Flushes the current proof writer and stop writing to it.
    ///
    /// Does nothing if no proof writer is currently active.
    pub fn close_proof(&mut self) -> std::io::Result<()> {
        if let Some(mut proof) = self.ctx.proof.take() {
            proof.flush()?;
        }
        Ok(())
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

impl HasLogger for Solver<'_> {
    #[inline(always)]
    fn logger(&self) -> &crate::log::Logger {
        self.ctx.logger()
    }
}
