//! This is currently very much an early work in progress and not yet usable.
#![warn(missing_docs)]

// Make the logging macros available crate-wide.
#[allow(unused_macros)]
macro_rules! info { ($($tt:tt)*) => { starlit_macros::info!($($tt)*) }; }
macro_rules! verbose { ($($tt:tt)*) => { starlit_macros::verbose!($($tt)*) }; }
macro_rules! debug { ($($tt:tt)*) => { starlit_macros::debug!($($tt)*) }; }
macro_rules! trace { ($($tt:tt)*) => { starlit_macros::trace!($($tt)*) }; }

pub mod clause_arena;
pub mod conflict_analysis;
pub mod context;
pub mod glue;
pub mod heap;
pub mod lit;
pub mod log;
pub mod minimize;
pub mod partial_assignment;
pub mod proof;
pub mod prop;
pub mod report;
pub mod search;
pub mod solver;
pub mod state;
pub mod stats;
pub mod tracking;
pub mod util;
