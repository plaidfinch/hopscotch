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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.push(0);
    /// assert_eq!(s.into_dense(), vec![Some(0)]);
    /// ```
    ///
    /// # Panics
    ///
    /// When the length of the sparse vector exceeds `usize::max_value()`.
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.push(100);
    /// s.skip(1);
    /// s.push(200);
    /// assert_eq!(s.pop(), Some(200));
    /// assert_eq!(s.pop(), None);
    /// assert_eq!(s.pop(), Some(100));
    /// assert_eq!(s.pop(), None);
    /// ```
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
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.skip(1);
    /// s.push(100);
    /// s.skip(2);
    /// s.push(200);
    /// s.skip(1);
    /// assert_eq!(s.into_dense(), vec![None, Some(100), None, None, Some(200), None]);
    /// ```
    ///
    /// # Panics
    ///
    /// If this operation would cause the length of the collection to exceed
    /// `usize::max_value()`.
    pub fn skip(&mut self, gap: usize) {
        self.end = self.end.checked_add(gap).expect("Sparse::skip: overflow")
    }

    /// Return an immutable reference to the value at the given `index`, or
    /// `None` if there is no value there or the length of the collection is too
    /// short.
    ///
    /// While `Vec::get` is constant-time, this operation is worst-case
    /// logarithmic in the length of the collection.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.skip(12345);
    /// s.push(100);
    /// assert_eq!(s.get(0), None);
    /// assert_eq!(s.get(12345), Some(&100));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        self.values.get(self.indices.binary_search(&index).ok()?)
    }

    /// Return a mutable reference to the value at the given `index`, or `None`
    /// if there is no value there or the length of the collection is too short.
    ///
    /// While `Vec::get` is constant-time, this operation is worst-case
    /// logarithmic in the length of the collection.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.skip(12345);
    /// s.push(100);
    /// s.get_mut(12345).map(|n| *n += 1);
    /// assert_eq!(s.get(12345), Some(&101));
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.values
            .get_mut(self.indices.binary_search(&index).ok()?)
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.push(1);
    /// s.push(2);
    /// s.push(3);
    /// s.clear();
    /// assert_eq!(s.into_dense(), vec![]);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.skip(12345);
    /// s.push(0);
    /// s.skip(54321);
    /// s.push(1);
    /// assert_eq!(s.count(), 2);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = Sparse::new();
    /// s.skip(9999);
    /// s.push(0);
    /// s.skip(9999);
    /// s.push(1);
    /// assert_eq!(s.len(), 20000);
    /// ```
    pub fn len(&self) -> usize {
        self.end
    }

    /// Return an iterator over the represented indices, paired with immutable
    /// references to the elements to which they correspond, in ascending order
    /// of index.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: self.indices.iter().copied().zip(self.values.iter()),
        }
    }

    /// Return an iterator over the represented indices, paired with mutable
    /// references to the elements to which they correspond, in ascending order
    /// of index.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            inner: self.indices.iter().copied().zip(self.values.iter_mut()),
        }
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

    /// Retains only the elements specified by the predicate.
    ///
    /// This method does not change the length of the resultant collection; it
    /// only removes elements from it without changing the effective length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::sparse::Sparse;
    /// let mut s: Sparse<usize> = (0..4).zip(0..4).collect();
    /// s.retain(|i, _| i % 2 == 0);
    /// assert_eq!(s.into_dense(), vec![Some(0), None, Some(2), None]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize, &mut T) -> bool,
    {
        let mut offset = 0;
        for count in 0..self.indices.len() {
            let index = self.indices[count];
            let value = self.values.get_mut(count).unwrap();
            if f(index, value) {
                self.values.swap(count, count - offset);
                self.indices.swap(count, count - offset);
            } else {
                offset += 1;
            }
        }
        self.indices.truncate(self.indices.len() - offset);
        self.values.truncate(self.values.len() - offset);
    }

    /// Shrink the capacity as much as possible, freeing currently unused
    /// memory.
    pub fn shrink_to_fit(&mut self) {
        self.indices.shrink_to_fit();
        self.values.shrink_to_fit();
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
        let mut result = Vec::with_capacity(self.end);
        for _ in 0..self.end {
            result.push(None);
        }
        for (i, a) in self.indices.into_iter().zip(self.values.into_iter()) {
            result[i] = Some(a);
        }
        result
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
            sparse.entry(index).insert(item);
        }
        sparse
    }
}

impl<T> Extend<(usize, T)> for Sparse<T> {
    fn extend<I: IntoIterator<Item = (usize, T)>>(&mut self, iter: I) {
        for (index, item) in iter {
            self.entry(index).insert(item);
        }
    }
}

impl<T> Default for Sparse<T> {
    fn default() -> Self {
        Sparse::new()
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
        IntoIter {
            inner: self.indices.into_iter().zip(self.values.into_iter()),
        }
    }
}
