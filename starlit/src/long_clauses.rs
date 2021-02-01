//! Storage of long clauses.
use std::mem::size_of;

use static_assertions::const_assert;

use crate::{
    lit::{Lit, LitIdx, Var},
    util::transparent::{AsStorage, AsStorageMut},
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

/// Data associated with a clause stored in [`LongClauses`].
#[repr(C)]
pub struct ClauseData {
    // SAFETY the MSB of any contained word must be zero
    data: LitIdx,
    /// Used to implement circular scanning during propagation
    ///
    /// See also ["Optimal Implementation of Watched Literals and More General
    /// Techniques"](https://doi.org/10.1613/jair.4016)
    search_pos: LitIdx,
}

impl ClauseData {
    /// Returns the circular scanning position used durig propagation.
    ///
    /// See also ["Optimal Implementation of Watched Literals and More General
    /// Techniques"](https://doi.org/10.1613/jair.4016)
    pub fn search_pos(&self) -> usize {
        self.search_pos as _
    }

    /// Updates the circular scanning position used durig propagation.
    pub fn set_search_pos(&mut self, search_pos: usize) {
        // SAFETY masking out the MSB maintains a safety invariant
        self.search_pos = (search_pos as LitIdx) & !LIT_IDX_MSB
    }
}

/// Header of a clause stored within [`LongClauses`].
#[repr(C)]
struct ClauseHeader {
    /// Further associated data
    data: ClauseData,
    /// Length of the clause with MSB set
    // SAFETY this must be the last word in this struct (with no padding)
    // TODO add assertions for this as soon as `ptr::addr_of` arrives in stable rust
    len_with_marker: LitIdx,
}

const LIT_IDX_MSB: LitIdx = !(!0 >> 1);

const_assert!(Lit::MAX_CODE < LIT_IDX_MSB as usize); // Ensure that the MSB of a Lit is not set

impl ClauseHeader {
    const WORDS: usize = size_of::<ClauseHeader>() / size_of::<LitIdx>();
    const LEN_OFFSET: usize = Self::WORDS - 1;

    pub fn new(len: usize) -> Self {
        assert!((LongClauses::MIN_LEN..=Var::MAX_VAR_COUNT).contains(&len));
        ClauseHeader {
            data: ClauseData {
                data: 0,
                search_pos: 2,
            },
            len_with_marker: (len as LitIdx) | LIT_IDX_MSB,
        }
    }
}

unsafe_impl_transparent!(ClauseHeader, [LitIdx; ClauseHeader::WORDS]);
/// Collection storing long clauses.
///
/// A clause is considered long if it has at least 3 literals.
#[derive(Default)]
pub struct LongClauses {
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
}

impl LongClauses {
    /// Minimal length of a long clause
    pub const MIN_LEN: usize = 3;

    /// Adds a new clause to the collection.
    pub fn add_clause(&mut self, clause_lits: &[Lit]) -> ClauseRef {
        let id = self.buffer.len();
        // TODO eventually this check should not panic
        assert!(id <= ClauseRefId::MAX as usize);
        let header = ClauseHeader::new(clause_lits.len());
        self.buffer.extend_from_slice(&header.as_storage());
        self.buffer.extend_from_slice(clause_lits.as_storage());
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
        let len_with_marker = self.buffer[clause.id as usize + ClauseHeader::LEN_OFFSET];
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
                .get_unchecked(clause.id as usize + ClauseHeader::WORDS..)
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
                .get_unchecked_mut(clause.id as usize + ClauseHeader::WORDS..)
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
    pub unsafe fn data_unchecked(&self, clause: ClauseRef) -> &ClauseData {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        let header = <&ClauseHeader>::from_storage_unchecked(
            &*(self.buffer.as_ptr().add(clause.id as usize)
                as *const [LitIdx; ClauseHeader::WORDS]),
        );

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
    pub unsafe fn data_unchecked_mut(&mut self, clause: ClauseRef) -> &mut ClauseData {
        #[cfg(debug_assertions)]
        self.clause_len(clause);

        let header = <&mut ClauseHeader>::from_storage_unchecked_mut(
            &mut *(self.buffer.as_mut_ptr().add(clause.id as usize)
                as *mut [LitIdx; ClauseHeader::WORDS]),
        );

        &mut header.data
    }

    /// Returns a reference to the associated data of a clause.
    ///
    /// Panics if the clause reference is invalid. Works on valid references to deleted clauses
    /// (which will be invalidated during the next garbage collection).
    pub fn data(&self, clause: ClauseRef) -> &ClauseData {
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
    pub fn data_mut(&mut self, clause: ClauseRef) -> &mut ClauseData {
        self.clause_len(clause);
        unsafe {
            // SAFETY `clause_len` panics if `clause` is invalid
            self.data_unchecked_mut(clause)
        }
    }

    /// Returns a [`ClauseRef`] to the next clause stored after `start` if such a clause exists.
    fn find_clause(&self, start: usize) -> Option<ClauseRef> {
        let mut pos = start + ClauseHeader::LEN_OFFSET;

        loop {
            let word = *self.buffer.get(pos)?;
            if word & LIT_IDX_MSB != 0 {
                if word == LIT_IDX_MSB {
                    // This is a deleted clause, next word contains the previous length of the
                    // deleted clause.
                    pos += self.buffer[pos + 1] as usize + ClauseHeader::WORDS;
                } else {
                    return Some(ClauseRef {
                        id: (pos - ClauseHeader::LEN_OFFSET) as _,
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
    /// # use starlit::long_clauses::LongClauses;
    /// let mut long_clauses = LongClauses::default();
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
            Some(clause) => (clause.id as usize) + self.clause_len(clause) + ClauseHeader::WORDS,
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
                .get_unchecked_mut(clause.id as usize + ClauseHeader::LEN_OFFSET) =
                LIT_IDX_MSB | (new_len as LitIdx);
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
                    .get_unchecked_mut(clause.id as usize + ClauseHeader::LEN_OFFSET) = LIT_IDX_MSB;
                *self
                    .buffer
                    .get_unchecked_mut(clause.id as usize + ClauseHeader::WORDS) = len as LitIdx;
            }
        }
    }
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
        let mut long_clauses = LongClauses::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(clause_lits));
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
    fn shrink_clauses() {
        let mut input_clauses = vec![
            clause![8, 9, 10, 11, 12, 13, 14, 15],
            clause![1, 2, 3],
            clause![4, 5, 6, 7],
            clause![16, 17, 18, 19, 20],
        ];
        let shrunk_lens = &[5, 3, 3, 4];
        let mut long_clauses = LongClauses::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(clause_lits));
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
        let mut long_clauses = LongClauses::default();

        let mut clause_refs = vec![];

        for clause_lits in &input_clauses {
            clause_refs.push(long_clauses.add_clause(clause_lits));
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
}
