use std::iter::{self, FromIterator};
use std::slice;
use std::vec;

pub mod entry;
use entry::*;

/// A `Sparse` vector is a memory-efficient representation of a vector where
/// many of the elements may not have a value. Think of `Sparse<T>` as analogous
/// to `Vec<Option<T>>`, where consecutive sequences of `None` are compressed. A
/// `Sparse<T>` takes up memory proportionate to its non-empty elements.
///
/// The main API attempts to mimic that of `std::vec::Vec`, with some slight
/// differences. However, it is also reasonable in some situations to treat a
/// `Sparse<T>` not as if it is a `Vec<Option<T>>`, but instead as if it is a
/// `HashMap<usize, T>`. For this idiom of use, see the `Entry` API, which
/// mimics the `Entry` API from `std::collections::HashMap`, and can be accessed
/// using the `entry` method.
#[derive(Debug, Clone)]
pub struct Sparse<T> {
    end: usize,
    indices: Vec<usize>,
    values: Vec<T>,
}

impl<T> Sparse<T> {
    /// Create a new, empty `Sparse<T>`.
    pub fn new() -> Sparse<T> {
        Self::with_capacity(0)
    }

    /// Create a new, empty `Sparse<T>` with the specified capacity.
    ///
    /// The vector will be able to hold exactly `capacity` elements without
    /// reallocating.
    pub fn with_capacity(capacity: usize) -> Sparse<T> {
        Sparse {
            end: 0,
            indices: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
        }
    }

    /// Append an element to the back of a `Sparse<T>`.
    pub fn push(&mut self, value: T) {
        self.indices.push(self.end);
        self.values.push(value);
        self.end = self.end.checked_add(1).expect("Sparse::push: overflow")
    }

    /// Remove the last element from a `Sparse<T>` and return it, or `None` if
    /// it is empty *or* if the corresponding element is not represented.
    ///
    /// This differs from `Vec::pop` in that it may return `None` when the
    /// length is greater than zero.
    pub fn pop(&mut self) -> Option<T> {
        self.end = self.end.saturating_sub(1);
        if let Some(i) = self.indices.last() {
            if *i == self.end {
                self.indices.pop();
                self.values.pop()
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Append a number of empty elements to the end of a `Sparse<T>`, such that
    /// there is a gap of size `gap` between the previous element and the next
    /// thing inserted.
    ///
    /// This operation is constant-time, regardless of the size of `gap`.
    ///
    /// If this operation would cause the length of the collection to exceed
    /// `usize::max_value()`, it panics.
    pub fn skip(&mut self, gap: usize) {
        self.end = self.end.checked_add(gap).expect("Sparse::skip: overflow")
    }

    /// Return an immutable reference to the value at the given `index`, or
    /// `None` if there is no value there or the length of the collection is too
    /// short.
    ///
    /// While `Vec::get` is constant-time, this operation is worst-case
    /// logarithmic in the length of the collection.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.values.get(self.indices.binary_search(&index).ok()?)
    }

    /// Return a mutable reference to the value at the given `index`, or `None`
    /// if there is no value there or the length of the collection is too short.
    ///
    /// While `Vec::get` is constant-time, this operation is worst-case
    /// logarithmic in the length of the collection.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.values.get_mut(self.indices.binary_search(&index).ok()?)
    }

    /// Return an `Entry` corresponding to the index specified, which may be
    /// either vacant or occupied, and which admits manipulation in-place. The
    /// index need not lie within the bounds of the collection: if a value is
    /// inserted at a vacant entry whose index is higher than the length of the
    /// collection, the length is extended to fit it.
    ///
    /// This operation takes time logarithmic in the number of entries in the
    /// sparse vector.
    pub fn entry(&mut self, index: usize) -> Entry<T> {
        match self.indices.binary_search(&index) {
            Ok(count) => Entry::Occupied(OccupiedEntry {
                count,
                indices: &mut self.indices,
                values: &mut self.values,
            }),
            Err(count) => Entry::Vacant(VacantEntry {
                count,
                index,
                indices: &mut self.indices,
                values: &mut self.values,
                end: &mut self.end,
            }),
        }
    }

    /// Clear the collection, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// collection.
    pub fn clear(&mut self) {
        self.indices.clear();
        self.values.clear();
        self.end = 0;
    }

    /// Count the number of values which are represented in the collection,
    /// *excluding* those which are skipped.
    ///
    /// For collections with no skipped indices, this will be equal to
    /// `Sparse::len`; otherwise, it will be strictly less.
    ///
    /// This operation is constant-time, regardless of the size of the
    /// collection.
    pub fn count(&self) -> usize {
        self.indices.len()
    }

    /// Return the number of elements in the collection, *including* those which
    /// are skipped.
    ///
    /// For collections with no skipped indices, this will be equal to
    /// `Sparse::count`; otherwise, it will be strictly greater.
    ///
    /// This operation is constant-time, regardless of the size of the
    /// collection.
    pub fn len(&self) -> usize {
        self.end
    }

    /// Return an iterator over the represented indices, paired with immutable
    /// references to the elements to which they correspond, in ascending order
    /// of index.
    pub fn iter(&self) -> Iter<T> {
        Iter { inner: self.indices.iter().copied().zip(self.values.iter()) }
    }

    /// Return an iterator over the represented indices, paired with mutable
    /// references to the elements to which they correspond, in ascending order
    /// of index.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut { inner: self.indices.iter().copied().zip(self.values.iter_mut()) }
    }

    /// Return an iterator over the indices which correspond to some element in
    /// the collection, in ascending order.
    pub fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.indices.iter().copied()
    }

    /// Return an iterator over just the values of the collection, omitting
    /// those which are skipped.
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.values.iter()
    }

    /// Return an iterator over just the values of the collection, omitting
    /// those which are skipped, which allows modifying each value.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.values.iter_mut()
    }

    /// Shrink the capacity as much as possible, freeing currently unused
    /// memory.
    pub fn shrink_to_fit(&mut self) {
        self.indices.shrink_to_fit();
        self.values.shrink_to_fit();
    }

    /// Return an iterator of immutable references to all the values represented
    /// in the collection, *including* those which have been skipped
    /// (represented as `None`).
    pub fn iter_dense(&self) -> IterDense<T> {
        IterDense {
            indices: &self.indices,
            values: self.values.iter(),
            end: self.end,
            index: 0,
        }
    }

    /// Return an iterator over mutable references to all the values represented
    /// in the collection, *including* those which have been skipped
    /// (represented as `None`).
    ///
    /// Note: this iterator does not allow removing or adding elements in the
    /// collection, or changing indices of existing elements.
    pub fn iter_dense_mut(&mut self) -> IterDenseMut<T> {
        IterDenseMut {
            indices: &self.indices,
            values: self.values.iter_mut(),
            end: self.end,
            index: 0,
        }
    }

    /// Return an iterator consuming the collection and returning all its
    /// values, *including* those which have been skipped (represented as
    /// `None`).
    pub fn into_iter_dense(self) -> IntoIterDense<T> {
        IntoIterDense {
            indices: self.indices,
            values: self.values.into_iter(),
            end: self.end,
            index: 0,
        }
    }

    /// Convert this `Sparse<T>` into a `Vec<Option<T>>` where `None` fills the
    /// place of any skipped elements.
    ///
    /// Keep in mind that the memory used by the resultant `Vec` will be
    /// proportionate to the length of the sparse collection: in the worst case,
    /// an empty sparse collection with length `usize::max_value()`, which is
    /// represented using only a few bytes, will be converted to a `Vec` of
    /// length `usize::max_value()`, which on most architectures is far too big
    /// to fit in RAM.
    pub fn into_dense(self) -> Vec<Option<T>> {
        self.into_iter_dense().collect()
    }
}

// Creating sparse vectors from iterators

impl<T> FromIterator<Option<T>> for Sparse<T> {
    fn from_iter<I: IntoIterator<Item = Option<T>>>(iter: I) -> Sparse<T> {
        let mut sparse = Sparse::new();
        for item in iter {
            match item {
                Some(x) => sparse.push(x),
                None => sparse.skip(1),
            }
        }
        sparse
    }
}

// TODO: make this optimal using co-sorting
impl<T> FromIterator<(usize, T)> for Sparse<T> {
    /// Create a sparse vector from an iterator of indices and values.
    ///
    /// Note: this takes time linear in the length of the iterator *if and only
    /// if* the indices are non-decreasing. If they are not in sorted order, it
    /// will take extra time, in the worst case (they are reversed) taking
    /// quadratic time.
    fn from_iter<I: IntoIterator<Item = (usize, T)>>(iter: I) -> Sparse<T> {
        let mut sparse = Sparse::new();
        for (index, item) in iter {
            sparse.entry(index).or_insert(item);
        }
        sparse
    }
}

// Iterating over `&T`

/// An iterator over pairs of indices and immutable references to values in a
/// `Sparse` vector.
pub struct Iter<'a, T> {
    inner: iter::Zip<std::iter::Copied<slice::Iter<'a, usize>>, slice::Iter<'a, T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a Sparse<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// Iterating over `&mut T`

/// An iterator over pairs of indices and mutable references to values in a
/// `Sparse` vector.
pub struct IterMut<'a, T> {
    inner: iter::Zip<std::iter::Copied<slice::Iter<'a, usize>>, slice::IterMut<'a, T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a mut Sparse<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// Iterating over `T`

/// An iterator over pairs of indices and values from a `Sparse` vector.
pub struct IntoIter<T> {
    inner: iter::Zip<vec::IntoIter<usize>, vec::IntoIter<T>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (usize, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> IntoIterator for Sparse<T> {
    type Item = (usize, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { inner: self.indices.into_iter().zip(self.values.into_iter()) }
    }
}

// Iterating densely over `&T`

/// An iterator over immutable references to all the items in a `Sparse`
/// collection, including those which have been skipped (represented as `None`).
///
/// This is produced by `Sparse::iter_dense()`.
pub struct IterDense<'a, T> {
    indices: &'a [usize],
    values: slice::Iter<'a, T>,
    end: usize,
    index: usize,
}

impl<'a, T> Iterator for IterDense<'a, T> {
    type Item = Option<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.end {
            None
        } else {
            let (first_index, rest_indices) = self.indices.split_first().unwrap();
            let result = if self.index == *first_index {
                let first_value = self.values.next().unwrap();
                self.indices = rest_indices;
                Some(first_value)
            } else {
                None
            };
            self.index += 1;
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.end, Some(self.end))
    }
}

// Iterating densely over `&mut T`

/// An iterator over mutable references to all the items in a `Sparse`
/// collection, including those which have been skipped (represented as `None`).
///
/// This is produced by `Sparse::iter_dense_mut()`.
pub struct IterDenseMut<'a, T> {
    indices: &'a [usize],
    values: slice::IterMut<'a, T>,
    end: usize,
    index: usize,
}

impl<'a, T> Iterator for IterDenseMut<'a, T> {
    type Item = Option<&'a mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.end {
            None
        } else {
            let (first_index, rest_indices) = self.indices.split_first().unwrap();
            let result = if self.index == *first_index {
                let first_value = self.values.next().unwrap();
                self.indices = rest_indices;
                Some(first_value)
            } else {
                None
            };
            self.index += 1;
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.end, Some(self.end))
    }
}

// Iterating densely over `T`

/// An iterator over all the items in a `Sparse` collection, including those
/// which have been skipped (represented as `None`).
///
/// This is produced by `Sparse::into_iter_dense()`.
pub struct IntoIterDense<T> {
    indices: Vec<usize>,
    values: vec::IntoIter<T>,
    end: usize,
    index: usize,
}

impl<T> Iterator for IntoIterDense<T> {
    type Item = Option<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.end {
            None
        } else {
            let first_index = self.indices.first().unwrap();
            let result = if self.index == *first_index {
                let first_value = self.values.next().unwrap();
                self.indices.pop();
                Some(first_value)
            } else {
                None
            };
            self.index += 1;
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.end, Some(self.end))
    }
}
