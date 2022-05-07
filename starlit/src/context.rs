//! Solver context (logging, etc.).
use crate::{
    log::{HasLogger, Logger},
    stats::Stats,
};

/// Solver context.
///
/// Stores everything that is part of a [`Solver`][crate::solver::Solver] but not part of the main solver [`State`][crate::state::State].
#[derive(Default)]
#[allow(missing_docs)]
pub struct Ctx {
    pub logger: Logger,
    pub stats: Stats,
}

impl HasLogger for Ctx {
    #[inline(always)]
    fn logger(&self) -> &Logger {
        &self.logger
    }
}
