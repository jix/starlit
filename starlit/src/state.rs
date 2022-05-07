//! Solver state.
use crate::{
    context::Ctx,
    report::report,
    search::{reduce, restart, search_step, Search},
    tracking::Resize,
};

use self::luby::LubySequence;

mod luby;

/// Stores the main state of a [`Solver`][crate::solver::Solver].
///
/// Some solver data that is used in many places is kept outside of this in [`Ctx`][crate::context::Ctx].
#[derive(Default)]
#[allow(missing_docs)]
pub struct State {
    pub search: Search,
    pub schedule: Schedule,
}

impl Resize for State {
    fn resize(&mut self, var_count: usize) {
        self.search.resize(var_count)
    }
}

/// Performs a scheduled action or one step of CDCL search and returns whether the formula is
/// satisfiable.
pub fn schedule_search_step(ctx: &mut Ctx, state: &mut State) -> Option<bool> {
    if should_restart(ctx, state) {
        restart(ctx, &mut state.search);
    }

    if should_reduce(ctx, state) {
        reduce(ctx, &mut state.search);
        report(ctx);
    }

    search_step(ctx, &mut state.search)
}

/// Restart and reduce schedule.
#[derive(Default)]
pub struct Schedule {
    next_restart: u64,
    restart_schedule: LubySequence,

    next_reduce: u64,
    reductions: u64,
}

/// Returns whether the search should restart.
fn should_restart(ctx: &mut Ctx, state: &mut State) -> bool {
    let restart = ctx.stats.search.conflicts >= state.schedule.next_restart;
    if restart {
        // TODO make scale configurable
        state.schedule.next_restart =
            ctx.stats.search.conflicts + state.schedule.restart_schedule.advance() * 512;
    }
    restart
}

/// Returns whether the clause database should be reduced.
fn should_reduce(ctx: &mut Ctx, state: &mut State) -> bool {
    let reduce = ctx.stats.search.conflicts >= state.schedule.next_reduce;
    if reduce {
        state.schedule.reductions += 1;
        state.schedule.next_reduce += (2000.0 * (state.schedule.reductions as f64).sqrt()) as u64;
    }
    reduce
}
