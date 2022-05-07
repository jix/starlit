//! Solver statistics

use crate::{
    prop::{FormulaStats, PropStats},
    search::SearchStats,
};

/// Solver statistics
#[allow(missing_docs)]
#[derive(Default)]
pub struct Stats {
    pub prop: PropStats,
    pub search: SearchStats,
    pub formula: FormulaStats,
}
