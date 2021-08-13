//! Literals and variables.

use std::{fmt, ops};

use crate::vec_map::{VecMapIndex, VecMapKey};

/// The backing type used to represent literals and variables.
pub type LitIdx = u32;

/// Signed integer with the same size and alignment of `LitIdx`.
pub type SignedLitIdx = i32;

/// A Boolean variable.
///
/// Internally Boolean variables are numbered starting from 0. This number is called the variable's
/// index.
///
/// For user I/O (including `Debug`) variables are numbered in the same order, but starting from 1.
/// This allows representing a negated variable using a negative integer which is the convention
/// also used by the DIMACS CNF format. Internally we call this number the DIMACS index or just
/// DIMACS, but avoid using it for anything besides user I/O.
///
/// There can be up to `Var::MAX_VAR_COUNT` variables numbered `0` to `Var::MAX_INDEX`. Here
/// `Var::MAX_INDEX` is smaller than `usize::MAX` and even smaller than `LitIdx::MAX`. This leaves
/// space for extra flags (as used by `Lit`) or sentinel values.
///
/// Note: Currently it is not possible to make this extra space available for Rust's niche
/// optimization. Instead, use a `LitIdx` or a wrapper around it to store a variable with flags or
/// sentinel values in the same number of bytes as a `Var` uses.
///
/// # Safety
///
/// Code in unsafe blocks may assume that a variable's index is constrained as described above.
/// Hence all safe methods for creating `Var` values check these. When using unsafe methods the
/// caller needs to ensure that these constraints hold.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Var {
    index: LitIdx,
}

impl Var {
    /// The largest supported index of a variable.
    ///
    /// This is less than the backing integer type supports. This enables storing a variable index
    /// and additional bits (as in `Lit`) or sentinel values in a single word.
    pub const MAX_INDEX: usize = (LitIdx::MAX >> 2) as usize;

    /// The number of representable variables.
    ///
    /// Exactly `Var::MAX_INDEX + 1`.
    pub const MAX_VAR_COUNT: usize = Var::MAX_INDEX + 1;

    /// The largest 1-based DIMACS index of a variable.
    /// Exactly `Var::MAX_INDEX + 1` but of type `isize`.
    pub const MAX_DIMACS: isize = Var::MAX_INDEX as isize + 1;

    /// Variable given in the representation used by the DIMACS CNF format.
    ///
    /// Panics if the parameter is not strictly positive or larger than `Var::MAX_DIMACS`.
    #[inline]
    pub fn from_dimacs(number: isize) -> Var {
        assert!(number > 0);
        Var::from_index((number - 1) as usize)
    }

    /// Variable of a given index.
    ///
    /// Panics when the index is larger than `Var::MAX_INDEX`.
    #[inline]
    pub fn from_index(index: usize) -> Var {
        assert!(index <= Var::MAX_INDEX);
        Var {
            index: index as LitIdx,
        }
    }

    /// Variable of a given index, without bounds checking.
    ///
    /// # Safety
    ///
    /// The index must not be larger than `Var::MAX_INDEX`.
    #[inline]
    pub unsafe fn from_index_unchecked(index: usize) -> Var {
        debug_assert!(index <= Var::MAX_INDEX);
        Var {
            index: index as LitIdx,
        }
    }

    /// Index of this variable.
    #[inline]
    pub const fn index(self) -> usize {
        self.index as usize
    }

    /// Representation used in the DIMACS CNF format.
    #[inline]
    pub fn dimacs(self) -> isize {
        (self.index + 1) as isize
    }
}

impl VecMapKey for Var {
    #[inline(always)]
    fn vec_map_key_from_index(index: usize) -> Self {
        Self::from_index(index)
    }
}

impl VecMapIndex for Var {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        self.index()
    }
}

/// As in the DIMACS CNF format.
impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.dimacs(), f)
    }
}

/// As in the DIMACS CNF format.
impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl flussab_cnf::Dimacs for Var {
    const MAX_DIMACS: isize = Var::MAX_DIMACS;

    fn from_dimacs(value: isize) -> Self {
        Var::from_dimacs(value)
    }

    fn dimacs(self) -> isize {
        Var::dimacs(self)
    }
}

/// A Boolean literal.
///
/// A literal is a variable or the negation of a variable.
///
/// A literal consists of a variable and a flag indicating the polarity (also called phase) of the
/// literal, i.e. whether the literal represents that variable (positive literal) or its negation
/// (negative literal).
///
/// Internally a literal is represented as an integer that is two times the index of its variable
/// when it is negative or one more when it is positive. This integer is called the `code` or
/// encoding of the literal.
///
/// The restriction on the range of allowed indices for `Var` also applies to `Lit`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Lit {
    code: LitIdx,
}

unsafe_impl_transparent!(Lit, LitIdx);

impl Lit {
    /// The largest supported code of a literal.
    ///
    /// This is less than the backing integer type supports. This enables storing a literal code
    /// and an additional bit or sentinel value in a single word.
    ///
    /// Equal to `2 * Var::MAX_INDEX + 1`.
    pub const MAX_CODE: usize = 2 * Var::MAX_INDEX + 1;

    /// A literal for a given variable.
    ///
    /// A positive literal if the second parameter is `true`, a negative literal otherwise.
    #[inline]
    pub fn from_var(var: Var, positive: bool) -> Lit {
        Lit {
            code: (var.index << 1) | (positive as LitIdx),
        }
    }

    /// A literal for the variable of a given index.
    ///
    /// Convenience method for the often needed `Lit::from_var(Var::from_index(index), positive)`.
    #[inline]
    pub fn from_index(index: usize, positive: bool) -> Lit {
        Lit::from_var(Var::from_index(index), positive)
    }

    /// A literal for the variable of a given index, without bounds checking.
    ///
    /// Convenience method for `Lit::from_var(Var::from_index_unchecked(index), positive)`.
    ///
    /// # Safety
    ///
    /// The index must not be larger than `Var::MAX_INDEX`.
    #[inline]
    pub unsafe fn from_index_unchecked(index: usize, positive: bool) -> Lit {
        Lit::from_var(Var::from_index_unchecked(index), positive)
    }

    /// A literal with a given encoding.
    ///
    /// Panics when the code is larger than `Lit::MAX_CODE`.
    #[inline]
    pub fn from_code(code: usize) -> Lit {
        assert!(code <= Lit::MAX_CODE);
        Lit {
            code: code as LitIdx,
        }
    }

    /// A literal with a given encoding, without bounds checking.
    ///
    /// Panics when the code is larger than `Lit::MAX_CODE`.
    ///
    /// # Safety
    ///
    /// The code must not be larger than `Lit::MAX_CODE`.
    #[inline]
    pub unsafe fn from_code_unchecked(code: usize) -> Lit {
        debug_assert!(code <= Lit::MAX_CODE);
        Lit {
            code: code as LitIdx,
        }
    }

    /// Literal given in the representation used by the DIMACS CNF format.
    ///
    /// Panics if the parameter is zero or has an absolute value larger than `Var::MAX_DIMACS`.
    #[inline]
    pub fn from_dimacs(number: isize) -> Lit {
        Lit::from_var(Var::from_dimacs(number.abs()), number > 0)
    }

    /// Encoding of this literal.
    #[inline]
    pub const fn code(self) -> usize {
        self.code as usize
    }

    /// The variable of this literal.
    #[inline]
    pub const fn var(self) -> Var {
        Var {
            index: self.code >> 1,
        }
    }

    /// Index of this literal's variable.
    #[inline]
    pub const fn index(self) -> usize {
        self.var().index()
    }

    /// Whether this is a positive literal.
    #[inline]
    pub const fn is_positive(self) -> bool {
        self.code & 1 != 0
    }

    /// Whether this is a negative literal.
    #[inline]
    pub const fn is_negative(self) -> bool {
        self.code & 1 == 0
    }

    /// Representation used in the DIMACS CNF format.
    #[inline]
    pub fn dimacs(self) -> isize {
        self.var().dimacs() as isize * if self.is_positive() { 1 } else { -1 }
    }

    /// Given two literals, one equal to this literal, returns the other.
    ///
    /// Returns an arbitrary literal or panics if none of the given literals are equal to this
    /// literal.
    #[inline]
    pub fn select_other(self, a: Lit, b: Lit) -> Lit {
        debug_assert!(self == a || self == b, "{:?} not in {:?} {:?}", self, a, b);
        Lit {
            code: self.code ^ a.code ^ b.code,
        }
    }
}

impl VecMapKey for Lit {
    #[inline(always)]
    fn vec_map_key_from_index(index: usize) -> Self {
        Self::from_code(index)
    }
}

impl VecMapIndex for Lit {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        self.code()
    }
}

impl VecMapIndex<Var> for Lit {
    #[inline(always)]
    fn vec_map_index(&self) -> usize {
        self.index()
    }
}

impl flussab_cnf::Dimacs for Lit {
    const MAX_DIMACS: isize = Var::MAX_DIMACS;

    fn from_dimacs(value: isize) -> Self {
        Lit::from_dimacs(value)
    }

    fn dimacs(self) -> isize {
        Lit::dimacs(self)
    }
}

impl ops::Not for Lit {
    type Output = Lit;

    fn not(self) -> Self::Output {
        Lit {
            code: self.code ^ 1,
        }
    }
}

/// As in the DIMACS CNF format.
impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.dimacs(), f)
    }
}

/// As in the DIMACS CNF format.
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}
