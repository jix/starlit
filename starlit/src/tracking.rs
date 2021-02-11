//! Traits for synchronizing updates that affect multiple solver components.

/// Solver component that requires updating when the number of variables change.
pub trait TracksVarCount {
    /// Current number of variables tracked by this solver component.
    fn var_count(&self) -> usize;

    /// Change the number of variables.
    ///
    /// Increases when new variables are added. Only decreases after all affected solver components
    /// are updated so the deleted vars are already unused.
    fn set_var_count(&mut self, var_count: usize);
}
