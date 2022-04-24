//! Using `Vec` as a map for various key types.

/// Wrapper for `Vec` when using it as a map with a key type that has a canonical mapping to
/// indices.
///
/// It is only possible to add or remove items at the end, i.e. the set of present keys must map to
/// `0..n` for some `n`.
#[repr(transparent)]
pub struct VecMap<Key, Value>(Vec<Value>, std::marker::PhantomData<Key>);

impl<Key, Value> VecMap<Key, Value> {
    /// Returns an iterator over the keys for which values are present.
    pub fn keys(&self) -> VecMapKeys<Key, std::ops::Range<usize>> {
        VecMapKeys::new(0..self.len())
    }
}

/// Wraps an `usize` yielding iterator as a `Key` yielding iterator.
pub struct VecMapKeys<Key, Inner>(Inner, std::marker::PhantomData<Key>);

impl<Key, Inner> VecMapKeys<Key, Inner> {
    /// Constructs a `Key` yielding iterator from a `usize` yielding iterator.
    fn new(inner: Inner) -> Self {
        Self(inner, std::marker::PhantomData)
    }
}

impl<Key, Inner> Iterator for VecMapKeys<Key, Inner>
where
    Inner: Iterator<Item = usize>,
    Key: VecMapKey,
{
    type Item = Key;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Key::vec_map_key_from_index)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    #[inline(always)]
    fn count(self) -> usize {
        self.0.count()
    }

    #[inline(always)]
    fn last(self) -> Option<Self::Item> {
        self.0.last().map(Key::vec_map_key_from_index)
    }

    #[inline(always)]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n).map(Key::vec_map_key_from_index)
    }
}

impl<Key, Inner> DoubleEndedIterator for VecMapKeys<Key, Inner>
where
    Inner: DoubleEndedIterator<Item = usize>,
    Key: VecMapKey,
{
    #[inline(always)]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Key::vec_map_key_from_index)
    }

    #[inline(always)]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n).map(Key::vec_map_key_from_index)
    }
}

impl<Key, Inner> ExactSizeIterator for VecMapKeys<Key, Inner>
where
    Inner: ExactSizeIterator<Item = usize>,
    Key: VecMapKey,
{
    #[inline(always)]
    fn len(&self) -> usize {
        self.0.len()
    }
}

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

impl<'a, Key, Value> IntoIterator for &'a VecMap<Key, Value> {
    type Item = &'a Value;

    type IntoIter = <&'a Vec<Value> as IntoIterator>::IntoIter;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}
