//! Starlit aims to be a somewhat modular SAT solver that exposes many solver internals.
//!
//! This is currently very much an early work in progress and not yet usable.
#![warn(missing_docs)]

#[macro_use]
pub mod util;

pub mod clauses;
pub mod conflict_analysis;
pub mod decision;
pub mod glue;
pub mod heap;
pub mod lit;
pub mod luby;
pub mod minimize;
pub mod phases;
pub mod reduce;
pub mod search;
pub mod solver;
pub mod tracking;
pub mod trail;
pub mod unit_prop;
pub mod vec_map;
