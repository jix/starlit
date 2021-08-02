//! Complete SAT solver interface.
//!
//! Groups all components necessary for the solver.
use crate::{luby::LubySequence, search::Search, tracking::TracksVarCount};

/// Contains all components of a SAT solver.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Solver {
    pub search: Search,
    pub restart: Restart,
}

impl TracksVarCount for Solver {
    fn var_count(&self) -> usize {
        self.search.var_count()
    }

    fn set_var_count(&mut self, var_count: usize) {
        self.search.set_var_count(var_count)
    }
}

impl Solver {
    /// Determines whether the current formula is satisfiable.
    pub fn solve(&mut self) -> bool {
        loop {
            if self.restart.should_restart(&self.search) {
                self.search.restart();
            }

            if let Some(verdict) = self.search.search_step() {
                return verdict;
            }
        }
    }
}

/// Restart schedule.
#[derive(Default)]
pub struct Restart {
    next: u64,
    schedule: LubySequence,
}

impl Restart {
    /// Returns whether the search should restart.
    fn should_restart(&mut self, search: &Search) -> bool {
        let restart = search.stats.conflicts >= self.next;
        if restart {
            // TODO make scale configurable
            self.next = search.stats.conflicts + self.schedule.advance() * 128;
        }
        restart
    }
}
