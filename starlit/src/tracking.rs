//! Traits for synchronizing updates that affect multiple solver components.

/// Solver component that requires updating when the number of variables change.
pub trait Resize {
    /// Change the number of variables.
    ///
    /// Increases when new variables are added. Only decreases after all affected solver components
    /// are updated so the deleted vars are already unused.
    fn resize(&mut self, var_count: usize);
}
