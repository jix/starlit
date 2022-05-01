//! Solver state.
use crate::{
    context::Ctx,
    search::{restart, search_step, Search},
    tracking::Resize,
};

use self::{luby::LubySequence, reduce::reduce};

mod luby;
mod reduce;

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
    if state.schedule.should_restart(&state.search) {
        restart(ctx, &mut state.search);
    }

    if state.schedule.should_reduce(&state.search) {
        reduce(ctx, &mut state.search);
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

impl Schedule {
    /// Returns whether the search should restart.
    fn should_restart(&mut self, search: &Search) -> bool {
        let restart = search.stats.conflicts >= self.next_restart;
        if restart {
            // TODO make scale configurable
            self.next_restart = search.stats.conflicts + self.restart_schedule.advance() * 512;
        }
        restart
    }

    /// Returns whether the clause database should be reduced.
    fn should_reduce(&mut self, search: &Search) -> bool {
        let reduce = search.stats.conflicts >= self.next_reduce;
        if reduce {
            self.reductions += 1;
            self.next_reduce += (2000.0 * (self.reductions as f64).sqrt()) as u64;
        }
        reduce
    }
}
