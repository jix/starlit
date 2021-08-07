//! Storage of long clauses.
use std::{cmp::Ordering, hint::unreachable_unchecked, mem::size_of, slice};

use starlit_macros::Bitfield;
use static_assertions::const_assert;

use crate::{
    lit::{Lit, LitIdx, Var},
    util::transparent::{ConvertStorage, ConvertStorageMut},
};

/// The backing type used to represent clause references.
type ClauseRefId = u32;

/// Reference to a long clause.
///
/// Identifies a clause stored by [`LongClauses`]. After garbage collection of the [`LongClauses`]
/// external references requies a fixup or they become invalid.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ClauseRef {
    id: ClauseRefId,
}

/// Data that can be safely stored with each clause in `LongClauses`.
///
/// # Safety
/// This is only safe to implement for types whose values have a representation equivalent to `[u32;
/// N]` for some `N` with each array element having an MSB of zero. This must also hold when
/// mutating values of the type. Allowing a MSB to become one is not memory safe when used in
/// `LongClauses`.
pub unsafe trait ClauseData: Copy {
    /// Called when size of the associated clause is decreases.
    ///
    /// This can be used to update data that might become invalid when this happens.
    fn shrink_clause(&mut self, len: usize);
}

/// Data associated with a clause during solving.
#[repr(C)]
#[derive(Bitfield, Clone, Copy, Default)]
pub struct SolverClauseData {
    // SAFETY the MSB of any contained word must be zero
    #[bitfield(
        /// whether the clause is redundant.
        1 => pub redundant: bool,
        /// whether the clause is protected.
        1 => pub protected: bool,
        /// the glue level of the clause.
        ///
        /// Also called Literal Block Distance (LBD).
        6 clamp => pub glue: usize,
        /// how often the clause was recently used.
        ///
        /// This is incremented everytime the clause is involved in a conflict and decremented
        /// during every reduction. Both increments and decrements are saturating.
        2 clamp => pub used: usize,
        1, // SAFETY reserve the MSB
    )]
    data: LitIdx,
    /// Used to implement circular scanning during propagation
    ///
    /// See also ["Optimal Implementation of Watched Literals and More General
    /// Techniques"](https://doi.org/10.1613/jair.4016)
    search_pos: LitIdx,
}

impl SolverClauseData {
    /// Returns new clause data for an input clause.
    pub fn new_input_clause() -> Self {
        Self::default()
    }

    /// Returns new clause data for a learned clause.
    pub fn new_learned_clause() -> Self {
        let mut data = Self::default();
        data.set_redundant(true);
        // Count the initial learning as use, so that the clause can survive an immediately
        // following reduction.
        data.set_used(1);
        data
    }
}

impl SolverClauseData {
    /// Returns the circular scanning position used durig propagation.
    ///
    /// Note that this starts counting with position 0 for the 3rd literal, i.e. skipping the
    /// watched literals.
    ///
    /// See also ["Optimal Implementation of Watched Literals and More General
    /// Techniques"](https://doi.org/10.1613/jair.4016)
    pub fn search_pos(&self) -> usize {
        self.search_pos as _
    }

    /// Updates the circular scanning position used durig propagation.
    ///
    /// Note that this starts counting with position 0 for the 3rd literal, i.e. skipping the
    /// watched literals.
    pub fn set_search_pos(&mut self, search_pos: usize) {
        // SAFETY masking out the MSB maintains a safety invariant
        self.search_pos = (search_pos as LitIdx) & !LIT_IDX_MSB
    }
}

// SAFETY the MSB of any contained word must be zero
unsafe impl ClauseData for SolverClauseData {
    fn shrink_clause(&mut self, _len: usize) {
        self.search_pos = 0;
    }
}

/// Header of a clause stored within [`LongClauses`].
#[repr(C)]
struct ClauseHeader<D: ClauseData> {
    /// Further associated data
    data: D,
    /// Length of the clause with MSB set
    // SAFETY this must be the last word in this struct (with no padding)
    // TODO add assertions for this as soon as `ptr::addr_of` arrives in stable rust
    len_with_marker: LitIdx,
}

const LIT_IDX_MSB: LitIdx = !(!0 >> 1);

const_assert!(Lit::MAX_CODE < LIT_IDX_MSB as usize); // Ensure that the MSB of a Lit is not set

impl<D: ClauseData> ClauseHeader<D> {
    const WORDS: usize = size_of::<Self>() / size_of::<LitIdx>();
    const LEN_OFFSET: usize = Self::WORDS - 1;

    pub fn new(data: D, len: usize) -> Self
    where
        D: Default,
    {
        assert!((LongClauses::<D>::MIN_LEN..=Var::MAX_VAR_COUNT).contains(&len));
        ClauseHeader {
            data,
            len_with_marker: (len as LitIdx) | LIT_IDX_MSB,
        }
    }
}

/// Collection storing long clauses.
///
/// A clause is considered long if it has at least 3 literals.
pub struct LongClauses<D: ClauseData = SolverClauseData> {
    // SAFETY see doc comment below
    /// Linear buffer storing all clauses.
    ///
    /// A [`ClauseRef`] indexes into this buffer and points at a [`ClauseHeader`] which is
    /// immediately followed by the clause's literals. The only words (`LitIdx` values) in the
    /// buffer which have their MSB set are the words containing the clause length. The clause
    /// length is contained in the last word of a clause header, directly preceeding the literals.
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
    /// previous length (without the MSB set). This is not a safety invariant, but setting that word
    /// to a value larger than the length will break clause iteration.
    buffer: Vec<LitIdx>,

    _marker: std::marker::PhantomData<D>,
}

impl<D: ClauseData> Default for LongClauses<D> {
    fn default() -> Self {
        Self {
            buffer: Default::default(),
            _marker: std::marker::PhantomData::<D>,
        }
    }
}

impl<D: ClauseData> LongClauses<D> {
    /// Minimal length of a long clause
    pub const MIN_LEN: usize = 3;

    /// Adds a new clause to the collection.
    pub fn add_clause(&mut self, data: D, clause_lits: &[Lit]) -> ClauseRef
    where
        D: Default,
    {
        let id = self.buffer.len();
        // TODO eventually this check should not panic
        assert!(id <= ClauseRefId::MAX as usize);
        let header = ClauseHeader::<D>::new(data, clause_lits.len());
        assert_eq!(
            ClauseHeader::<D>::WORDS * size_of::<LitIdx>(),
            size_of::<ClauseHeader::<D>>()
        );
        self.buffer.extend_from_slice(unsafe {
            // SAFETY allowed due to `D: ClauseData` and the assert above
            std::slice::from_raw_parts(
                &header as *const _ as *const LitIdx,
                ClauseHeader::<D>::WORDS,
            )
        });
        self.buffer.extend_from_slice(clause_lits.into_storage());
        ClauseRef { id: id as _ }
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
        let len_with_marker = self.buffer[clause.id as usize + ClauseHeader::<D>::LEN_OFFSET];
        // SAFETY this check ensures that an invalid ClausRef is detected
        if len_with_marker & LIT_IDX_MSB == 0 {
            panic!("invalid ClauseRef");
        }
        (len_with_marker & !LIT_IDX_MSB) as usize
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
                .get_unchecked(clause.id as usize + ClauseHeader::<D>::WORDS..)
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
                .get_unchecked_mut(clause.id as usize + ClauseHeader::<D>::WORDS..)
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

    /// Returns a reference to the associated data of a clause without validity or bounds checking.
    ///
    /// Works on valid references to deleted clauses (which will be invalidated during the next
    /// garbage collection).
    ///
    /// # Safety
    /// Here `clause` needs to be valid.
    pub unsafe fn data_unchecked(&self, clause: ClauseRef) -> &D {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        let header = &*(self.buffer.as_ptr().add(clause.id as usize) as *const ClauseHeader<D>);

        &header.data
    }

    /// Returns a mutable reference to the associated data of a clause without validity or bounds
    /// checking.
    ///
    /// Works on valid references to deleted clauses (which will be invalidated during the next
    /// garbage collection).
    ///
    /// # Safety
    /// Here `clause` needs to be valid.
    pub unsafe fn data_unchecked_mut(&mut self, clause: ClauseRef) -> &mut D {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        let header =
            &mut *(self.buffer.as_mut_ptr().add(clause.id as usize) as *mut ClauseHeader<D>);

        &mut header.data
    }

    /// Returns a reference to the associated data of a clause.
    ///
    /// Panics if the clause reference is invalid. Works on valid references to deleted clauses
    /// (which will be invalidated during the next garbage collection).
    pub fn data(&self, clause: ClauseRef) -> &D {
        self.clause_len(clause);
        unsafe {
            // SAFETY `clause_len` panics if `clause` is invalid
            self.data_unchecked(clause)
        }
    }

    /// Returns a mutable reference to the associated data of a clause.
    ///
    /// Panics if the clause reference is invalid. Works on valid references to deleted clauses
    /// (which will be invalidated during the next garbage collection).
    pub fn data_mut(&mut self, clause: ClauseRef) -> &mut D {
        self.clause_len(clause);
        unsafe {
            // SAFETY `clause_len` panics if `clause` is invalid
            self.data_unchecked_mut(clause)
        }
    }

    /// Returns a reference to the literals and associated data of a clause without validity or
    /// bounds checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice for the literals.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn data_and_lits_unchecked_with_len(
        &self,
        clause: ClauseRef,
        len: usize,
    ) -> (&D, &[Lit]) {
        debug_assert_eq!(self.clause_len(clause), len);
        let ptr = self.buffer.as_ptr().add(clause.id as usize);
        let header = &*(ptr as *const ClauseHeader<D>);
        let lits = <&[Lit]>::from_storage_unchecked(slice::from_raw_parts(
            ptr.add(ClauseHeader::<D>::WORDS),
            len,
        ));
        (&header.data, lits)
    }

    /// Returns a mutable reference to the literals and associated data of a clause without validity
    /// or bounds checking.
    ///
    /// For a valid reference to a deleted clause (which will be invalidated during the next garbage
    /// collection), this returns an empty slice  for the literals.
    ///
    /// # Safety
    /// Here `clause` needs to be valid and `len` needs to be the actualy length of the
    /// corresponding clause.
    pub unsafe fn data_and_lits_unchecked_with_len_mut(
        &mut self,
        clause: ClauseRef,
        len: usize,
    ) -> (&mut D, &mut [Lit]) {
        debug_assert_eq!(self.clause_len(clause), len);
        let ptr = self.buffer.as_mut_ptr().add(clause.id as usize);
        let header = &mut *(ptr as *mut ClauseHeader<D>);
        let lits = <&mut [Lit]>::from_storage_unchecked_mut(slice::from_raw_parts_mut(
            ptr.add(ClauseHeader::<D>::WORDS),
            len,
        ));
        (&mut header.data, lits)
    }

    /// Returns a reference to the literals and associated data of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn data_and_lits(&self, clause: ClauseRef) -> (&D, &[Lit]) {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.data_and_lits_unchecked_with_len(clause, self.clause_len(clause)) }
    }

    /// Returns a mutable reference to the literals and associated data of a clause.
    ///
    /// Panics if the clause reference is invalid. For a valid reference to a deleted clause (which
    /// will be invalidated during the next garbage collection), this returns an empty slice.
    pub fn data_and_lits_mut(&mut self, clause: ClauseRef) -> (&mut D, &mut [Lit]) {
        // SAFETY clause_len panics when `clause` is invalid
        unsafe { self.data_and_lits_unchecked_with_len_mut(clause, self.clause_len(clause)) }
    }

    /// Returns a [`ClauseRef`] to the next clause stored after `start` if such a clause exists.
    fn find_clause(&self, start: usize) -> Option<ClauseRef> {
        let mut pos = start + ClauseHeader::<D>::LEN_OFFSET;

        loop {
            let word = *self.buffer.get(pos)?;
            if word & LIT_IDX_MSB != 0 {
                if word == LIT_IDX_MSB {
                    // This is a deleted clause, next word contains the previous length of the
                    // deleted clause.
                    pos += self.buffer[pos + 1] as usize + ClauseHeader::<D>::WORDS;
                } else {
                    return Some(ClauseRef {
                        id: (pos - ClauseHeader::<D>::LEN_OFFSET) as _,
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
    /// # use starlit::clauses::long::{LongClauses, SolverClauseData};
    /// let mut long_clauses = LongClauses::<SolverClauseData>::default();
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
            Some(clause) => {
                (clause.id as usize) + self.clause_len(clause) + ClauseHeader::<D>::WORDS
            }
        };
        *clause = self.find_clause(start);
        *clause
    }

    /// Shrink the size of a clause, dropping final literals.
    ///
    /// Panics when the new size is larger than the initial size or smaller than
    /// [`LongClauses::MIN_LEN`].
    pub fn shrink_clause(&mut self, clause: ClauseRef, new_len: usize) {
        let len = self.clause_len(clause);
        assert!((Self::MIN_LEN..=len).contains(&new_len));
        unsafe {
            // SAFETY `clause_len` above asserts that `clause` is valid
            *self
                .buffer
                .get_unchecked_mut(clause.id as usize + ClauseHeader::<D>::LEN_OFFSET) =
                LIT_IDX_MSB | (new_len as LitIdx);

            // The search_pos might now point past the last element of the clause, so we reset it.
            self.data_unchecked_mut(clause).shrink_clause(new_len);
        }
    }

    /// Deletes a clause, marking it for garbage collection.
    ///
    /// The clause reference stays valid until the next garbage collection, but accessing a deleted
    /// clause's literals will return an empty slice.
    pub fn delete_clause(&mut self, clause: ClauseRef) {
        let len = self.clause_len(clause);
        if len > 0 {
            unsafe {
                // SAFETY `clause_len` above asserts that `clause` is valid
                *self
                    .buffer
                    .get_unchecked_mut(clause.id as usize + ClauseHeader::<D>::LEN_OFFSET) =
                    LIT_IDX_MSB;
                *self
                    .buffer
                    .get_unchecked_mut(clause.id as usize + ClauseHeader::<D>::WORDS) =
                    len as LitIdx;
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
            let storage_size = self.clause_len(clause) + ClauseHeader::<D>::WORDS;
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

        ClauseRefGcMap { gaps }
    }
}

/// Used to update [`ClauseRef`] values after [`LongClauses::collect_garbage`].
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
        let mut long_clauses = LongClauses::<SolverClauseData>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(SolverClauseData::default(), clause_lits));
        }

        let mut current_clause = None;
        let mut expected = input_clauses.iter().zip(&clause_refs);
        while let Some(clause_ref) = long_clauses.next_clause(&mut current_clause) {
            let (expected_lits, &expected_clause_ref) = expected.next().unwrap();
            assert_eq!(clause_ref, expected_clause_ref);
            assert_eq!(expected_lits, long_clauses.lits(clause_ref));
            assert_eq!(expected_lits, long_clauses.lits_mut(clause_ref));
            assert_eq!(expected_lits, long_clauses.data_and_lits(clause_ref).1);
            assert_eq!(expected_lits, long_clauses.data_and_lits_mut(clause_ref).1);
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
        let mut long_clauses = LongClauses::<SolverClauseData>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(SolverClauseData::default(), clause_lits));
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
        let mut long_clauses = LongClauses::<SolverClauseData>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(SolverClauseData::default(), clause_lits));
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

        let mut long_clauses = LongClauses::<SolverClauseData>::default();

        let mut expected_clause_refs = vec![];

        for clause_lits in &input_clauses {
            let clause = long_clauses.add_clause(SolverClauseData::default(), clause_lits);
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
        let mut long_clauses = LongClauses::<SolverClauseData>::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(SolverClauseData::default(), clause_lits));
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
