//! Compact storage for clauses of varying length.
use std::{cmp::Ordering, hint::unreachable_unchecked};

use crate::{
    lit::{Lit, LitIdx},
    util::transparent::{ConvertStorage, ConvertStorageMut, Transparent},
};

/// The backing type used to represent clause references.
type ClauseRefId = u32;

/// Reference to clause inside the arena.
///
/// Identifies a clause stored by [`ClauseArena`]. After garbage collection of the [`ClauseArena`]
/// external references requies a fixup or they become invalid.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[repr(transparent)]
pub struct ClauseRef {
    id: ClauseRefId,
}

/// A `LitIdx` with the most significant bit unset.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default, Transparent, Debug)]
#[repr(transparent)]
pub struct HeaderWord {
    data: LitIdx,
}

const HEADER_MASK: LitIdx = LitIdx::MAX >> 1;
const LEN_MARKER: LitIdx = !HEADER_MASK;

impl HeaderWord {
    /// Returns a [`HeaderWord`] containing `data` with the most significant bit unset.
    pub fn new(data: LitIdx) -> Self {
        Self {
            data: data & HEADER_MASK,
        }
    }

    /// Returns a bit at a fixed position within the word.
    pub fn bit<const BIT: u32>(self) -> bool {
        assert!(BIT < LitIdx::BITS - 1);
        self.data & (1 << BIT) != 0
    }

    /// Sets a bit at a fixed position within the word.
    pub fn set_bit<const BIT: u32>(&mut self, value: bool) {
        assert!(BIT < LitIdx::BITS - 1);
        self.data = (self.data & !(1 << BIT)) | ((value as LitIdx) << BIT);
    }

    /// Returns an integer stored at a fixed range of bits within the word.
    pub fn field<const START: u32, const WIDTH: u32>(self) -> LitIdx {
        assert!(START + WIDTH <= LitIdx::BITS - 1);
        (self.data >> START) & ((1 << WIDTH) - 1)
    }

    /// Sets an integer stored at a fixed range of bits within the word.
    ///
    /// If the passed value is larger than can be stored in the range of bits, the largest value
    /// that fits is stored instead.
    pub fn set_field<const START: u32, const WIDTH: u32>(&mut self, mut value: LitIdx) {
        assert!(START + WIDTH <= LitIdx::BITS - 1);
        if value > ((1 << WIDTH) - 1) {
            value = (1 << WIDTH) - 1;
        }

        self.data = (self.data & !(((1 << WIDTH) - 1) << START)) | (value << START);
    }
}

impl From<HeaderWord> for LitIdx {
    fn from(word: HeaderWord) -> Self {
        word.data
    }
}

/// A [`ClauseHeader`] containing no data.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Transparent, Default)]
#[repr(C)]
pub struct EmptyClauseHeader(pub [HeaderWord; 0]);

impl ClauseHeader for EmptyClauseHeader {}

/// Type that can be stored as a clause header within a [`ClauseArena`].
pub trait ClauseHeader: Transparent {
    /// Updates a `ClauseHeader` when the number of clause literals is reduced.
    #[inline]
    #[allow(unused_variables)]
    fn shrink_clause(&mut self, old_len: usize, new_len: usize) {}
}

/// Error type returned when adding a clause would exceed the range of [`ClauseRef`].
#[derive(Debug)]
pub struct ArenaSpaceExhausted;

/// Compact storage for many clauses with varying clause lengths.
pub struct ClauseArena<Header> {
    // SAFETY see doc comment below
    /// Linear buffer storing all clauses.
    ///
    /// A [`ClauseRef`] indexes into this buffer and points at a fixed size [`ClauseHeader`]
    /// followed by the clauses's length and then the clause's literals. The only words (`LitIdx`
    /// values) in the buffer which have their MSB set are the words containing the clause length.
    ///
    /// The MSB is used to detect clauses during iteration as well as to verify the validity of any
    /// passed [`ClauseRef`] values. The stored length is trusted and assumed to be in bounds, so
    /// all code modifying any value stored within the buffer must make sure that no safe call can
    /// produce words with their MSB set inadvertently.
    ///
    /// There may be arbitrary padding words between clauses, as long as those words do not have
    /// their MSB set. This happens for example when shrinking clauses.
    ///
    /// When a clause is deleted, its size is set to zero. In that case, to still allow fast
    /// iteration over clauses, the first literal of the clause is replaced with the clause's
    /// previous length (without the MSB set).
    buffer: Vec<LitIdx>,

    /// Number of words in `buffer` corresponding to deleted clauses.
    garbage_count: usize,

    _marker: std::marker::PhantomData<Header>,
}

impl<Header> Default for ClauseArena<Header> {
    fn default() -> Self {
        Self {
            buffer: vec![],
            garbage_count: 0,
            _marker: std::marker::PhantomData,
        }
    }
}

fn array_ptr<T, const LEN: usize>(first: *const T) -> *const [T; LEN] {
    first.cast()
}

fn array_mut_ptr<T, const LEN: usize>(first: *mut T) -> *mut [T; LEN] {
    first.cast()
}

impl<Header, const HEADER_LEN: usize> ClauseArena<Header>
where
    Header: ClauseHeader<Storage = [HeaderWord; HEADER_LEN]>,
{
    /// Adds a new clause to the collection.
    ///
    /// Panics when `lits` is empty.
    pub fn add_clause(
        &mut self,
        header: Header,
        lits: &[Lit],
    ) -> Result<ClauseRef, ArenaSpaceExhausted> {
        assert!(!lits.is_empty());
        let id = self.buffer.len();
        if id > ClauseRefId::MAX as usize || lits.len() > HEADER_MASK as usize {
            return Err(ArenaSpaceExhausted);
        }
        let grow = lits.len() + HEADER_LEN + 1;
        self.buffer.reserve(grow);
        unsafe {
            let mut spare = self.buffer.as_mut_ptr().add(self.buffer.len());

            array_mut_ptr::<_, HEADER_LEN>(spare).write(header.into_storage().into_storage());
            spare = spare.add(HEADER_LEN);
            spare.write((lits.len() as LitIdx) | LEN_MARKER);
            spare = spare.add(1);
            spare.copy_from_nonoverlapping(lits.into_storage().as_ptr(), lits.len());
            self.buffer.set_len(self.buffer.len() + grow);
        }
        Ok(ClauseRef { id: id as _ })
    }

    /// Returns the length of a clause.
    ///
    /// This will panic if the passed clause reference is invalid and thus can be used to assert the
    /// validity of a clause reference.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns zero and can be used to detect such references.
    pub fn clause_len(&self, clause: ClauseRef) -> usize {
        // Equivalent to calling `unwrap` on the result of `try_clause_len`.
        let len_with_marker = self.buffer[clause.id as usize + HEADER_LEN];
        // SAFETY this check ensures that an invalid ClausRef is detected
        if len_with_marker & LEN_MARKER == 0 {
            panic!("invalid ClauseRef");
        }
        (len_with_marker & HEADER_MASK) as usize
    }

    /// Returns a reference to the literals of a clause without validity or bounds checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn lits_unchecked_with_len(&self, clause: ClauseRef, len: usize) -> &[Lit] {
        debug_assert_eq!(self.clause_len(clause), len);

        <&[Lit]>::from_storage_unchecked(
            self.buffer
                .get_unchecked(clause.id as usize + HEADER_LEN + 1..)
                .get_unchecked(..len),
        )
    }

    /// Returns a mutable reference to the literals of a clause without validity or bounds checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn lits_unchecked_with_len_mut(
        &mut self,
        clause: ClauseRef,
        len: usize,
    ) -> &mut [Lit] {
        debug_assert_eq!(self.clause_len(clause), len);

        <&mut [Lit]>::from_storage_unchecked_mut(
            self.buffer
                .get_unchecked_mut(clause.id as usize + HEADER_LEN + 1..)
                .get_unchecked_mut(..len),
        )
    }

    /// Returns a reference to the literals of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn lits(&self, clause: ClauseRef) -> &[Lit] {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.lits_unchecked_with_len(clause, self.clause_len(clause)) }
    }

    /// Returns a mutable reference to the literals of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn lits_mut(&mut self, clause: ClauseRef) -> &mut [Lit] {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.lits_unchecked_with_len_mut(clause, self.clause_len(clause)) }
    }

    /// Returns a reference to the header of a clause without validity or bounds checking.
    ///
    /// Works on valid references to deleted clauses (which will be invalidated during the next
    /// garbage collection).
    ///
    /// # Safety
    /// Here `clause` needs to be valid.
    pub unsafe fn header_unchecked(&self, clause: ClauseRef) -> &Header {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        <&Header>::from_storage_unchecked(<&_>::from_storage_unchecked(
            &*array_ptr::<_, HEADER_LEN>(self.buffer.as_ptr().add(clause.id as usize)),
        ))
    }

    /// Returns a mutable reference to the header of a clause without validity or bounds checking.
    ///
    /// Works on valid references to deleted clauses (which will be invalidated during the next
    /// garbage collection).
    ///
    /// # Safety
    /// Here `clause` needs to be valid.
    pub unsafe fn header_unchecked_mut(&mut self, clause: ClauseRef) -> &mut Header {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        <&mut Header>::from_storage_unchecked_mut(<&mut _>::from_storage_unchecked_mut(
            &mut *array_mut_ptr::<_, HEADER_LEN>(self.buffer.as_mut_ptr().add(clause.id as usize)),
        ))
    }

    /// Returns a reference to the header of a clause.
    ///
    /// Panics if the clause reference is invalid. Works on valid references to deleted clauses
    /// (which will be invalidated during the next garbage collection).
    pub fn header(&self, clause: ClauseRef) -> &Header {
        self.clause_len(clause);
        unsafe {
            // SAFETY `clause_len` panics if `clause` is invalid
            self.header_unchecked(clause)
        }
    }

    /// Returns a mutable reference to the header of a clause.
    ///
    /// Panics if the clause reference is invalid. Works on valid references to deleted clauses
    /// (which will be invalidated during the next garbage collection).
    pub fn header_mut(&mut self, clause: ClauseRef) -> &mut Header {
        self.clause_len(clause);
        unsafe {
            // SAFETY `clause_len` panics if `clause` is invalid
            self.header_unchecked_mut(clause)
        }
    }

    /// Returns a reference to the literals and header of a clause without validity or bounds
    /// checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice for the literals.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn header_and_lits_unchecked_with_len(
        &self,
        clause: ClauseRef,
        len: usize,
    ) -> (&Header, &[Lit]) {
        debug_assert_eq!(self.clause_len(clause), len);

        (
            <&Header>::from_storage_unchecked(<&_>::from_storage_unchecked(&*array_ptr::<
                _,
                HEADER_LEN,
            >(
                self.buffer.as_ptr().add(clause.id as usize),
            ))),
            <&[Lit]>::from_storage_unchecked(
                self.buffer
                    .get_unchecked(clause.id as usize + HEADER_LEN + 1..)
                    .get_unchecked(..len),
            ),
        )
    }

    /// Returns a mutable reference to the literals and header of a clause without validity or
    /// bounds checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice  for the literals.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn header_and_lits_unchecked_with_len_mut(
        &mut self,
        clause: ClauseRef,
        len: usize,
    ) -> (&mut Header, &mut [Lit]) {
        debug_assert_eq!(self.clause_len(clause), len);

        (
            <&mut Header>::from_storage_unchecked_mut(<&mut _>::from_storage_unchecked_mut(
                &mut *array_mut_ptr::<_, HEADER_LEN>(
                    self.buffer.as_mut_ptr().add(clause.id as usize),
                ),
            )),
            <&mut [Lit]>::from_storage_unchecked_mut(
                self.buffer
                    .get_unchecked_mut(clause.id as usize + HEADER_LEN + 1..)
                    .get_unchecked_mut(..len),
            ),
        )
    }

    /// Returns a reference to the literals and header of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn header_and_lits(&self, clause: ClauseRef) -> (&Header, &[Lit]) {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.header_and_lits_unchecked_with_len(clause, self.clause_len(clause)) }
    }

    /// Returns a mutable reference to the literals and header of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn header_and_lits_mut(&mut self, clause: ClauseRef) -> (&mut Header, &mut [Lit]) {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.header_and_lits_unchecked_with_len_mut(clause, self.clause_len(clause)) }
    }

    /// Returns a [`ClauseRef`] to the next clause stored after `start` if such a clause exists.
    fn find_clause(&self, start: usize) -> Option<ClauseRef> {
        let mut pos = start + HEADER_LEN;

        loop {
            let word = *self.buffer.get(pos)?;
            if word & LEN_MARKER != 0 {
                if word == LEN_MARKER {
                    // This is a deleted clause, next word contains the previous length of the
                    // deleted clause.
                    pos += self.buffer[pos + 1] as usize + HEADER_LEN + 1;
                } else {
                    return Some(ClauseRef {
                        id: (pos - HEADER_LEN) as _,
                    });
                }
            } else {
                pos += 1;
            }
        }
    }

    /// Iterates over all clauses.
    ///
    /// Updates the passed reference to point to the next clause. If the passed values was `None`,
    /// it will point it at the first clause. If there is no next (or first) clause, the passed
    /// reference will be set to `None`. Returns the updated value of the passed reference.
    ///
    /// This allows iteration using the following pattern:
    /// ```rust
    /// # use starlit::clause_arena::{ClauseArena, EmptyClauseHeader};
    /// let mut long_clauses = ClauseArena::<EmptyClauseHeader>::default();
    /// // ...
    /// let mut clause_iter = None;
    /// while let Some(clause) = long_clauses.next_clause(&mut clause_iter) {
    ///     let lits = long_clauses.lits(clause);
    ///     // ...
    /// }
    /// ```
    pub fn next_clause(&self, clause: &mut Option<ClauseRef>) -> Option<ClauseRef> {
        let start = match *clause {
            None => 0,
            Some(clause) => (clause.id as usize) + self.clause_len(clause) + HEADER_LEN + 1,
        };
        *clause = self.find_clause(start);
        *clause
    }

    /// Shrink the size of a clause, dropping final literals.
    ///
    /// Panics when the new size is zero or larger than the clause's current size.
    pub fn shrink_clause(&mut self, clause: ClauseRef, new_len: usize) {
        assert_ne!(new_len, 0);
        let len = self.clause_len(clause);
        assert!(new_len <= len);

        self.garbage_count += len - new_len;

        unsafe {
            // SAFETY `clause_len` above asserts that `clause` is valid
            *self
                .buffer
                .get_unchecked_mut(clause.id as usize + HEADER_LEN) =
                LEN_MARKER | (new_len as LitIdx);

            // The header might have to be updated when the clause size changes.
            self.header_unchecked_mut(clause)
                .shrink_clause(len, new_len);
        }
    }

    /// Deletes a clause, marking it for garbage collection.
    ///
    /// The clause reference stays valid until the next garbage collection, but accessing a deleted
    /// clause's literals will return an empty slice.
    pub fn delete_clause(&mut self, clause: ClauseRef) {
        let len = self.clause_len(clause);
        self.garbage_count += len + HEADER_LEN + 1;
        if len > 0 {
            unsafe {
                // SAFETY `clause_len` above asserts that `clause` is valid
                *self
                    .buffer
                    .get_unchecked_mut(clause.id as usize + HEADER_LEN) = LEN_MARKER;
                *self
                    .buffer
                    .get_unchecked_mut(clause.id as usize + HEADER_LEN + 1) = len as LitIdx;
            }
        }
    }

    /// Reclaims memory used by deleted clauses.
    ///
    /// This invalidates all `ClauseRef` values, but also returns a mapping of previously valid
    /// `ClauseRefs` to the new corresponding valid `ClauseRefs`.
    pub fn collect_garbage(&mut self) -> ClauseRefGcMap {
        let mut read = None;
        let mut write_offset = 0;
        let mut expected_read_offset = 0;

        let mut gaps = vec![];

        // For garbage collection we use a slightly modified `next_clause` iteration that reads one
        // step ahead, so we can safely move the current clause without breaking the iteration.
        self.next_clause(&mut read);
        while let Some(clause) = read {
            self.next_clause(&mut read); // we are free to move `clause` below here
            let storage_size = self.clause_len(clause) + HEADER_LEN + 1;
            let read_offset = clause.id as usize;
            if read_offset != expected_read_offset {
                gaps.push(GcMapGap {
                    start: expected_read_offset as LitIdx,
                    end: read_offset as LitIdx,
                    shift: (read_offset - write_offset) as LitIdx,
                });
            }
            expected_read_offset = read_offset + storage_size;
            self.buffer
                .copy_within(read_offset..read_offset + storage_size, write_offset);
            write_offset += storage_size;
        }

        // Detect a gap at the end of the buffer
        let read_offset = self.buffer.len();
        if read_offset != expected_read_offset {
            gaps.push(GcMapGap {
                start: expected_read_offset as LitIdx,
                end: read_offset as LitIdx,
                shift: (read_offset - write_offset) as LitIdx,
            });
        }

        self.buffer.truncate(write_offset);

        self.garbage_count = 0;

        ClauseRefGcMap { gaps }
    }

    /// Returns whether the buffer is at least half full with garbage.
    pub fn should_collect_garbage(&self) -> bool {
        self.garbage_count * 2 >= self.buffer.len()
    }

    /// Returns the length of the allocated buffer and the number of words used for clause storage.
    pub fn utilization(&self) -> Utilization {
        let allocated = self.buffer.len();
        Utilization {
            allocated,
            used: allocated - self.garbage_count,
        }
    }
}

/// Length of the allocated buffer and the number of words used for clause storage.
#[derive(Debug)]
pub struct Utilization {
    /// Length of the allocated buffer.
    pub allocated: usize,
    /// Number of words used for clause storage.
    pub used: usize,
}

/// Used to update [`ClauseRef`] values after [`ClauseArena::collect_garbage`].
///
/// A garbage collection invaldiates all [`ClauseRef`] values, but this map can be used to update
/// them so they become valid again.
pub struct ClauseRefGcMap {
    gaps: Vec<GcMapGap>,
}

impl ClauseRefGcMap {
    /// Update a pre-collection to a post-collection [`ClauseRef`].
    ///
    /// For a valid-pre-collection non-deleted clause reference a corresponding
    /// valid-post-collection clause reference is returned. For a valid-pre-collection deleted
    /// clause reference this returns `None`. If the given clause reference was not valid
    /// pre-collection, the result is an unspecified, possibly invalid clause reference, but calling
    /// this is still safe and will not panic.
    pub fn update(&self, clause: ClauseRef) -> Option<ClauseRef> {
        // Find the gap containing or directly preceeding `clause`. This considers `gap.start` to
        // point between words and `clause.id` to point at a word, to avoid the `Ordering::Equal`
        // case.
        if let Err(index) = self.gaps.binary_search_by(|gap| {
            if gap.start > clause.id {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }) {
            // The index returned by binary_search is an ordered insertion index, so it is one
            // larger than the index of the found gap. If it is zero there is no preceeding gap.
            if let Some(gap) = self.gaps.get(index.wrapping_sub(1)) {
                debug_assert!(gap.start <= clause.id);
                if gap.end > clause.id {
                    None
                } else {
                    Some(ClauseRef {
                        id: clause.id - gap.shift,
                    })
                }
            } else {
                // No preceeding gap means the clause did not move during collection
                Some(clause)
            }
        } else {
            unsafe {
                // SAFETY our binary_search_by callback never returns `Ordering::Equal`
                unreachable_unchecked();
            }
        }
    }
}

/// Range of reclaimed storage during garbage collection.
///
/// Used in [`ClauseRefGcMap`].
struct GcMapGap {
    /// Start of a removed range of (pre-collection) [`ClauseRef`] ids.
    start: LitIdx,
    /// End of a removed range of (pre-collection) [`ClauseRef`] ids.
    end: LitIdx,
    /// Value to subtract from pre-collection ids to get post-collection ids for clauses between
    /// this gap and the following gap.
    shift: LitIdx,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default, Transparent)]
    #[repr(transparent)]
    struct TestHeader {
        words: [HeaderWord; 1],
    }

    impl ClauseHeader for TestHeader {
        fn shrink_clause(&mut self, _old_len: usize, new_len: usize) {
            self.words[0] = HeaderWord::new(new_len as _);
        }
    }

    macro_rules! clause {
        ($($lit:expr),*) => {
            vec![$(Lit::from_dimacs($lit)),*]
        };
    }

    #[test]
    fn iter_clauses() {
        let input_clauses = vec![
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![8, 9, 10, 11, 12],
        ];
        let mut long_clauses = ClauseArena::<TestHeader>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(
                long_clauses
                    .add_clause(TestHeader::default(), clause_lits)
                    .unwrap(),
            );
        }

        let mut current_clause = None;
        let mut expected = input_clauses.iter().zip(&clause_refs);
        while let Some(clause_ref) = long_clauses.next_clause(&mut current_clause) {
            let (expected_lits, &expected_clause_ref) = expected.next().unwrap();
            assert_eq!(clause_ref, expected_clause_ref);
            assert_eq!(expected_lits, long_clauses.lits(clause_ref));
            assert_eq!(expected_lits, long_clauses.lits_mut(clause_ref));
            assert_eq!(expected_lits, long_clauses.header_and_lits(clause_ref).1);
            assert_eq!(
                expected_lits,
                long_clauses.header_and_lits_mut(clause_ref).1
            );
        }
        assert_eq!(expected.next(), None);
    }

    #[test]
    fn shrink_clauses() {
        let mut input_clauses = vec![
            clause![8, 9, 10, 11, 12, 13, 14, 15],
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![16, 17, 18, 19, 20],
        ];
        let shrunk_lens = &[5, 3, 3, 4];
        let mut long_clauses = ClauseArena::<TestHeader>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(
                long_clauses
                    .add_clause(TestHeader::default(), clause_lits)
                    .unwrap(),
            );
        }

        for ((&clause, &shrunk_len), input_clause) in
            clause_refs.iter().zip(shrunk_lens).zip(&mut input_clauses)
        {
            long_clauses.shrink_clause(clause, shrunk_len);
            input_clause.resize(shrunk_len, Lit::from_dimacs(1));
        }

        let mut current_clause = None;
        let mut expected = input_clauses.iter().zip(&clause_refs);
        while let Some(clause_ref) = long_clauses.next_clause(&mut current_clause) {
            let (expected_lits, &expected_clause_ref) = expected.next().unwrap();
            assert_eq!(clause_ref, expected_clause_ref);
            assert_eq!(expected_lits, long_clauses.lits(clause_ref));
            assert_eq!(expected_lits, long_clauses.lits_mut(clause_ref));
        }
        assert_eq!(expected.next(), None);
    }

    #[test]
    fn delete_clauses() {
        let mut input_clauses = vec![
            clause![8, 9, 10, 11, 12, 13, 14, 15],
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![21, 22, 23],
            clause![16, 17, 18, 19, 20],
            clause![24, 25, 26],
        ];
        let delete_indices = &[2, 0, 3];
        let mut long_clauses = ClauseArena::<TestHeader>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(
                long_clauses
                    .add_clause(TestHeader::default(), clause_lits)
                    .unwrap(),
            );
        }

        for &index in delete_indices {
            long_clauses.delete_clause(clause_refs[index]);
            input_clauses[index].clear();
        }

        for &index in delete_indices {
            assert!(long_clauses.lits(clause_refs[index]).is_empty());
        }

        let mut current_clause = None;
        let mut expected = input_clauses
            .iter()
            .zip(&clause_refs)
            .filter(|(clause, _)| !clause.is_empty());
        while let Some(clause_ref) = long_clauses.next_clause(&mut current_clause) {
            let (expected_lits, &expected_clause_ref) = expected.next().unwrap();
            assert_eq!(clause_ref, expected_clause_ref);
            assert_eq!(expected_lits, long_clauses.lits(clause_ref));
            assert_eq!(expected_lits, long_clauses.lits_mut(clause_ref));
        }
        assert_eq!(expected.next(), None);
    }

    #[test]
    fn delete_while_iterating() {
        let input_clauses = vec![
            clause![8, 9, 10, 11, 12, 13, 14, 15],
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![21, 22, 23],
            clause![16, 17, 18, 19, 20],
            clause![24, 25, 26],
        ];

        let mut long_clauses = ClauseArena::<TestHeader>::default();

        let mut expected_clause_refs = vec![];

        for clause_lits in &input_clauses {
            let clause = long_clauses
                .add_clause(TestHeader::default(), clause_lits)
                .unwrap();
            if clause_lits[0].index() & 1 != 0 {
                expected_clause_refs.push(clause);
            }
        }

        let mut clause_iter = None;
        while let Some(clause) = long_clauses.next_clause(&mut clause_iter) {
            if long_clauses.lits(clause)[0].index() & 1 == 0 {
                long_clauses.delete_clause(clause);
            }
        }

        let mut clauses_left = vec![];

        let mut clause_iter = None;
        while let Some(clause) = long_clauses.next_clause(&mut clause_iter) {
            clauses_left.push(clause);
        }

        assert_eq!(clauses_left, expected_clause_refs);
    }

    #[test]
    fn collect_deleted_clauses() {
        let mut input_clauses = vec![
            clause![8, 9, 10, 11, 12, 13, 14, 15],
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![21, 22, 23],
            clause![16, 17, 18, 19, 20],
            clause![24, 25, 26],
        ];
        let delete_indices = &[2, 0, 3, 5];
        let mut long_clauses = ClauseArena::<TestHeader>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(
                long_clauses
                    .add_clause(TestHeader::default(), clause_lits)
                    .unwrap(),
            );
        }

        for &index in delete_indices {
            long_clauses.delete_clause(clause_refs[index]);
            input_clauses[index].clear();
        }

        let gc_map = long_clauses.collect_garbage();

        let mut current_clause = None;
        let mut expected = input_clauses
            .iter()
            .zip(&clause_refs)
            .filter(|(clause, _)| !clause.is_empty());
        while let Some(clause_ref) = long_clauses.next_clause(&mut current_clause) {
            let (expected_lits, &expected_clause_ref) = expected.next().unwrap();
            assert_eq!(clause_ref, gc_map.update(expected_clause_ref).unwrap());
            assert_eq!(expected_lits, long_clauses.lits(clause_ref));
            assert_eq!(expected_lits, long_clauses.lits_mut(clause_ref));
        }
        assert_eq!(expected.next(), None);

        for (clause, &clause_ref) in input_clauses.iter().zip(&clause_refs) {
            if clause.is_empty() {
                assert_eq!(gc_map.update(clause_ref), None);
            }
        }
    }

    #[test]
    fn clause_ref_gc_map() {
        #[rustfmt::skip]
        let map = ClauseRefGcMap {
            gaps: vec![
                GcMapGap { start: 5, end: 10, shift: 5 },
                GcMapGap { start: 15, end: 20, shift: 10 },
            ],
        };

        assert_eq!(map.update(ClauseRef { id: 0 }), Some(ClauseRef { id: 0 }));
        assert_eq!(map.update(ClauseRef { id: 4 }), Some(ClauseRef { id: 4 }));
        assert_eq!(map.update(ClauseRef { id: 5 }), None);
        assert_eq!(map.update(ClauseRef { id: 9 }), None);
        assert_eq!(map.update(ClauseRef { id: 10 }), Some(ClauseRef { id: 5 }));
        assert_eq!(map.update(ClauseRef { id: 14 }), Some(ClauseRef { id: 9 }));
        assert_eq!(map.update(ClauseRef { id: 15 }), None);
        assert_eq!(map.update(ClauseRef { id: 19 }), None);
        assert_eq!(map.update(ClauseRef { id: 20 }), Some(ClauseRef { id: 10 }));
        assert_eq!(
            map.update(ClauseRef { id: LitIdx::MAX }),
            Some(ClauseRef {
                id: LitIdx::MAX - 10
            })
        );

        #[rustfmt::skip]
        let map = ClauseRefGcMap {
            gaps: vec![
                GcMapGap { start: 0, end: 5, shift: 5 },
                GcMapGap { start: 15, end: 20, shift: 10 },
            ],
        };
        assert_eq!(map.update(ClauseRef { id: 0 }), None);
        assert_eq!(map.update(ClauseRef { id: 4 }), None);
        assert_eq!(map.update(ClauseRef { id: 5 }), Some(ClauseRef { id: 0 }));
    }
}
