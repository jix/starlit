//! Addressable heaps.
use std::{mem::swap, ops::Index};

use crate::lit::LitIdx;

/// Addressable max heap.
///
/// This also stores values for indices currently not on the heap.
///
/// Implemented as a binary heap of indices with an extra array that tracks each index's position in
/// the heap.
#[derive(Debug)]
pub struct MaxHeap<V> {
    values: Vec<V>,
    heap_pos: Vec<LitIdx>,
    heap: Vec<LitIdx>,
}

impl<V> Default for MaxHeap<V> {
    fn default() -> Self {
        Self {
            values: vec![],
            heap_pos: vec![],
            heap: vec![],
        }
    }
}

macro_rules! swap {
    ($s:expr, $pos_a:expr, $pos_b:expr) => {
        $s.heap.swap($pos_a, $pos_b);
        $s.heap_pos
            .swap($s.heap[$pos_a] as usize, $s.heap[$pos_b] as usize);
        swap(&mut $pos_a, &mut $pos_b);
    };
}

impl<V: Ord> MaxHeap<V> {
    /// Resize the array of values, using the given value to initalize new values.
    ///
    /// This does not enqueue indices when growing, but will dequeue removed indices when
    /// shrinking.
    pub fn resize(&mut self, len: usize, value: V)
    where
        V: Clone,
    {
        assert!(len <= (LitIdx::MAX as usize) + 1);

        if len < self.values.len() {
            for index in len..self.values.len() {
                self.dequeue(index);
            }
        }

        self.values.resize(len, value);
        self.heap_pos.resize(len, !0);
    }

    /// Returns the size of the array of values.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns whether the index is enqueued.
    pub fn is_enqueued(&self, index: usize) -> bool {
        (self.heap_pos[index] as usize) < self.heap.len()
    }

    /// Dequeue the index.
    ///
    /// No-op when the index was not enqueued.
    pub fn dequeue(&mut self, index: usize) {
        let mut pos = self.heap_pos[index] as usize;
        if pos >= self.heap.len() {
            return;
        }

        let mut other_pos = self.heap.len() - 1;

        #[allow(clippy::branches_sharing_code)] // clippy#7369
        if other_pos == pos {
            self.heap_pos[index] = !0;
            self.heap.pop();
        } else {
            swap!(self, other_pos, pos);
            self.heap_pos[index] = !0;
            self.heap.pop();

            if self.values[self.heap[other_pos] as usize] > self.values[index] {
                self.move_towards_leaves(other_pos)
            } else {
                self.move_towards_root(other_pos)
            }
        }
    }

    /// Enqueue the index.
    ///
    /// No-op when the index is already enqueued.
    pub fn enqueue(&mut self, index: usize) {
        let mut pos = self.heap_pos[index] as usize;
        if pos < self.heap.len() {
            return;
        }

        pos = self.heap.len();
        self.heap.push(index as LitIdx);
        self.heap_pos[index] = pos as LitIdx;

        self.move_towards_root(pos);
    }

    /// Dequeue and return the index with the largest value.
    pub fn pop_max(&mut self) -> Option<usize> {
        if self.heap.is_empty() {
            return None;
        }

        let mut pos = 0;
        let index = self.heap[pos] as usize;

        let mut other_pos = self.heap.len() - 1;

        #[allow(clippy::branches_sharing_code)] // clippy#7369
        if other_pos == pos {
            self.heap_pos[index] = !0;
            self.heap.pop();
        } else {
            swap!(self, other_pos, pos);

            self.heap_pos[index] = !0;
            self.heap.pop();

            self.move_towards_leaves(other_pos)
        }

        Some(index)
    }

    /// Move value at `pos` towards the root until it stops having a smaller parent.
    fn move_towards_root(&mut self, mut pos: usize) {
        let value = &self.values[self.heap[pos] as usize];
        while pos > 0 {
            let mut parent_pos = (pos - 1) / 2;
            if self.values[self.heap[parent_pos] as usize] < *value {
                swap!(self, pos, parent_pos);
            } else {
                break;
            }
        }
    }

    /// Move value at `pos` towards the leaves until it stops having larger children.
    ///
    /// Always select the larger child as target to maintain the heap property.
    fn move_towards_leaves(&mut self, mut pos: usize) {
        let value = &self.values[self.heap[pos] as usize];

        loop {
            let left_child_pos = pos * 2 + 1;

            let mut smallest_pos = pos;
            let mut smallest_value = value;

            if left_child_pos < self.heap.len()
                && *smallest_value < self.values[self.heap[left_child_pos] as usize]
            {
                smallest_pos = left_child_pos;
                smallest_value = &self.values[self.heap[left_child_pos] as usize];
            }

            let right_child_pos = pos * 2 + 2;

            if right_child_pos < self.heap.len()
                && *smallest_value < self.values[self.heap[right_child_pos] as usize]
            {
                smallest_pos = right_child_pos;
            }

            if smallest_pos == pos {
                break;
            }

            swap!(self, pos, smallest_pos);
        }
    }

    /// Increase the value for the given index.
    ///
    /// Can be called whether the index is enqueued or not. The passed function may not decrease the
    /// given value. (Doing so is memory safe, but breaks internal invariants.)
    pub fn increase(&mut self, index: usize, f: impl FnOnce(&mut V)) {
        f(&mut self.values[index]);

        let pos = self.heap_pos[index] as usize;
        if pos < self.heap.len() {
            self.move_towards_root(pos);
        }
    }

    /// Apply a (weakly) monotone function to all values.
    ///
    /// Passing a function that is not weakly monotone, is not allowed.  (Doing so is memory safe,
    /// but breaks internal invariants.)
    pub fn apply_monotone(&mut self, f: impl Fn(&mut V)) {
        for value in &mut self.values {
            f(value);
        }
    }
}

impl<V> Index<usize> for MaxHeap<V> {
    type Output = V;

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enqueue_some_increase_pop() {
        let mut heap = MaxHeap::<usize>::default();

        heap.resize(10, 0);

        for i in 0..10 {
            if i % 3 > 0 {
                heap.enqueue(i);
            }
        }

        for i in 0..10 {
            heap.increase(i, |v| *v += 2 * i);
        }

        let mut ordered = vec![];

        while let Some(index) = heap.pop_max() {
            ordered.push(index);
        }

        assert_eq!(ordered, [8, 7, 5, 4, 2, 1]);
    }
}
