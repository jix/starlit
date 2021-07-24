//! Scan over a [`Vec`] with mutation and removal of items.
//!
//! This is a subset of the functionality provided by the `vec_mut_scan` library, but more optimized
//! for our unit propagation implementation. Eventually these improvements should land in
//! `vec_mut_scan` but having this limited to just the functionality we are actually using makes it
//! easier to optimize it for our use here.
//!
//! One difference to `vec_mut_scan` is that dropping a wrapped item removes it and you need to call
//! `keep` to avoid that.
use std::{intrinsics::copy, ops::Range};

// SAFETY notes for the whole mod.
// Here is a small overview of how this is implemented:

// The initial state after taking ownership of the data from `Vec` looks like this (with the length
// of the vector temporarily set to zero):

//   |start = write = read      |end
//   [a][b][c][d][e][f][g][h][i]

// If the read pointer is not at the end, calling `next` returns the item (wrapped in a
// `MutScanItem`) and advances the read pointer.

//   |start = write
//   |  |read                   |end
//    u [b][c][d][e][f][g][h][i]         item = [a]

// This creates a gap of uninitialized memory between the write and the read pointer.

// Calling `keep` on the wrapped item places it back (after potentially modifying or replacing it)
// by writing it to the write pointer and advancing it:

//   |start
//   |  |write = read           |end
//   [A][b][c][d][e][f][g][h][i]

// This means that whenever a wrapped item is alive, the write pointer must point to the first
// uninitialized position of the `Vec`'s buffer and such a position must exist.

// After calling next again we have the following situation:

//   |start
//   |  |write
//   |  |  |read                |end
//   [A] u [c][d][e][f][g][h][i]        item = [b]

// Dropping the wrapped item or calling `remove` to unwrap it does not change any pointers or values
// in the `Vec`'s buffer. After doing that we can call next again and get a larger grap:

//   |start
//   |  |write
//   |  |     |read             |end
//   [A] u  u [d][e][f][g][h][i]        item = [c]

// Calling `keep` on the item then writes it back to a different position from where it was read
// from:

//   |start
//   |     |write
//   |     |  |read             |end
//   [A][C] u [d][e][f][g][h][i]

// Finally, dropping the scan itself, moves the remaining items between the read and end pointer to
// close the gap between the write and read pointer, followed by updating the length of the vector
// to the number of remaining items.

//   [A][C][d][e][f][g][h][i] u

// When leaking the scan instead of dropping it, the `Vec` still has a length of zero, which is
// safe, but leaks the content of the buffer.

/// Scan over a [`Vec`] with mutation and removal of items.
pub struct MutScan<'a, T> {
    vec: &'a mut Vec<T>,
    end: *mut T,
    read: *mut T,
    write: *mut T,
}

impl<'a, T> MutScan<'a, T> {
    /// Creates a new scan over a [`Vec`].
    pub fn new(vec: &'a mut Vec<T>) -> Self {
        let Range { start, end } = vec.as_mut_ptr_range();

        unsafe {
            // SAFETY Perform leak amplification in case this scan is leaked.
            vec.set_len(0);
        }

        Self {
            vec,
            end,
            read: start,
            write: start,
        }
    }

    /// Returns the next item, wrapped in a [`MutScanItem`].
    #[inline(always)]
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<MutScanItem<'_, 'a, T>> {
        if self.read == self.end {
            None
        } else {
            unsafe {
                // SAFETY see module level safety comment
                let item = self.read.read();
                self.read = self.read.add(1);

                Some(MutScanItem { scan: self, item })
            }
        }
    }
}

impl<'a, T> Drop for MutScan<'a, T> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY see module level safety comment
            let suffix_len = self.end.offset_from(self.read) as usize;
            copy(self.read, self.write, suffix_len);
            self.read = self.read.add(suffix_len);
            self.write = self.write.add(suffix_len);

            let final_len = self.write.offset_from(self.vec.as_mut_ptr()) as usize;

            self.vec.set_len(final_len);
        }
    }
}

/// Wraps the current item of a [`MutScan`].
///
/// Allows placing the item back into the scanned [`Vec`] or removing it. By default, when dropping
/// the `MutScanItem` the wrapped item is dropped and removed from the [`Vec`].
pub struct MutScanItem<'a, 'b, T> {
    scan: &'a mut MutScan<'b, T>,
    item: T,
}

impl<'a, 'b, T> std::ops::Deref for MutScanItem<'a, 'b, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<'a, 'b, T> std::ops::DerefMut for MutScanItem<'a, 'b, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}

impl<'a, 'b, T> MutScanItem<'a, 'b, T> {
    /// Places the item back into the scanned [`Vec`].
    #[inline(always)]
    pub fn keep(self) {
        unsafe {
            // SAFETY see module level safety comment
            self.scan.write.write(self.item);
            self.scan.write = self.scan.write.add(1);
        }
    }

    /// Returns the item, removing it from the scanned [`Vec`].
    #[inline(always)]
    pub fn remove(self) -> T {
        self.item
    }
}
