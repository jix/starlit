//! Complete SAT solver interface.
//!
//! Groups all components necessary for the solver.
use crate::{luby::LubySequence, reduce::ReduceOps, search::Search, tracking::TracksVarCount};

/// Contains all components of a SAT solver.
#[derive(Default)]
#[allow(missing_docs)]
pub struct Solver {
    pub search: Search,
    pub schedule: Schedule,
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
            if self.schedule.should_restart(&self.search) {
                self.search.restart();
            }

            if self.schedule.should_reduce(&self.search) {
                ReduceOps {
                    search: &mut self.search,
                }
                .reduce();
            }

            if let Some(verdict) = self.search.search_step() {
                return verdict;
            }
        }
    }
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
