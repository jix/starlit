//! Using `Vec` as a map for various key types.

/// Wrapper for `Vec` when using it as a map with a key type that has a canonical mapping to
/// indices.
///
/// It is only possible to add or remove items at the end, i.e. the set of present keys must map to
/// `0..n` for some `n`.
#[repr(transparent)]
pub struct VecMap<Key, Value>(Vec<Value>, std::marker::PhantomData<Key>);

/// Type that can be used as key for `VecMap`.
pub trait VecMapKey: VecMapIndex + Sized {
    /// Constructs a key from the array index.
    ///
    /// This may only panic for indices which cannot be returned by any corresponding
    /// [`vec_map_index`](VecMapIndex::vec_map_index) implementation.
    fn vec_map_key_from_index(index: usize) -> Self;
}

/// Type that can be used to access an item in a `VecMap`.
///
/// This allows using multiple types to index the same `VecMap`, which is useful if there is a
/// canonical conversion e.g. from literals to variables.
pub trait VecMapIndex<Key = Self> {
    /// Returns the corresponding index for a key.
    fn vec_map_index(&self) -> usize;
}

impl VecMapIndex for usize {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        *self
    }
}

impl VecMapKey for usize {
    fn vec_map_key_from_index(index: usize) -> Self {
        index
    }
}

impl<Key, Value> Default for VecMap<Key, Value> {
    #[inline(always)]
    fn default() -> Self {
        VecMap(vec![], std::marker::PhantomData)
    }
}

impl<Key, Value> Clone for VecMap<Key, Value>
where
    Value: Clone,
{
    #[inline(always)]
    fn clone(&self) -> Self {
        Self::from(self.0.clone())
    }
}

impl<Key, Value> std::fmt::Debug for VecMap<Key, Value>
where
    Value: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

impl<Key, Value> From<Vec<Value>> for VecMap<Key, Value> {
    #[inline(always)]
    fn from(vec: Vec<Value>) -> Self {
        VecMap(vec, std::marker::PhantomData)
    }
}

impl<Key, Value> std::ops::Deref for VecMap<Key, Value> {
    type Target = Vec<Value>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Key, Value> std::ops::DerefMut for VecMap<Key, Value> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<Key, Value, I: VecMapIndex<Key>> std::ops::Index<I> for VecMap<Key, Value> {
    type Output = Value;

    #[inline(always)]
    fn index(&self, index: I) -> &Self::Output {
        self.0.index(index.vec_map_index())
    }
}

impl<Key, Value, I: VecMapIndex<Key>> std::ops::IndexMut<I> for VecMap<Key, Value> {
    #[inline(always)]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.0.index_mut(index.vec_map_index())
    }
}
