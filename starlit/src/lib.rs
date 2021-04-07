//! Starlit aims to be a somewhat modular SAT solver that exposes many solver internals.
//!
//! This is currently very much an early work in progress and not yet usable.
#![warn(missing_docs)]

#[macro_use]
pub mod util;

pub mod clauses;
pub mod conflict_analysis;
pub mod lit;
pub mod tracking;
pub mod trail;
pub mod unit_prop;
