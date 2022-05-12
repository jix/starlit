//! Solver context (logging, etc.).
use crate::{
    log::{HasLogger, Logger},
    proof::Proof,
    stats::Stats,
};

/// Solver context.
///
/// Stores everything that is part of a [`Solver`][crate::solver::Solver] but not part of the main solver [`State`][crate::state::State].
#[derive(Default)]
#[allow(missing_docs)]
pub struct Ctx<'a> {
    pub logger: Logger,
    pub stats: Stats,
    pub proof: Option<Box<dyn Proof + 'a>>,
}

impl HasLogger for Ctx<'_> {
    #[inline(always)]
    fn logger(&self) -> &Logger {
        &self.logger
    }
}
