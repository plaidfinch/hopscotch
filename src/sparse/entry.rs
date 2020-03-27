/// A view into a single entry in a `Sparse` vector, which may be vacant or
/// occupied. The index of the entry need not be currently within the bounds of
/// the collection; inserting at the location will extend the collection as
/// appropriate.
///
/// This API is modeled after the `Entry` API from the standard library's
/// `HashMap` implementation, intended to let you treat a `Sparse<T>` as a
/// `HashMap<usize, T>`.
///
/// Note: the operations here have different asymptotics than those of a
/// `HashMap`. In particular: insertions and removals are amortized constant
/// time only when they occur at the end of the sparse vector. When they occur
/// in the middle, they take time proportionate to the number of occupied
/// entries with index higher than theirs.
pub enum Entry<'a, T> {
    Occupied(OccupiedEntry<'a, T>),
    Vacant(VacantEntry<'a, T>),
}

impl<'a, T> Entry<'a, T> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Returns the index to which this entry corresponds.
    pub fn index(&self) -> usize {
        match self {
            Entry::Occupied(entry) => entry.index(),
            Entry::Vacant(entry) => entry.index(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the sparse vector.
    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            },
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut T where T: Default {
        self.or_insert(T::default())
    }
}

/// A view into an occupied entry in a `Sparse` vector. It is part of the
/// `Entry` enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, T> {
    pub(super) count: usize,
    pub(super) indices: &'a mut Vec<usize>,
    pub(super) values: &'a mut Vec<T>,
}

impl<'a, T> OccupiedEntry<'a, T> {
    /// Get the index of this entry in the sparse vector to which it belongs.
    pub fn index(&self) -> usize {
        self.indices[self.count]
    }

    /// Take ownership of the value and its index, and remove it from the sparse
    /// vector.
    ///
    /// Note that this *does not* change the index of any other elements of the
    /// collection, nor does it change the length of the collection.
    ///
    /// This operation is linear in time proportionate to the number of entries
    /// with index higher than the index of this entry (which is to say, it is
    /// constant time if this is the last item in the collection).
    pub fn remove_entry(self) -> (usize, T) {
        let i = self.indices.remove(self.count);
        let a = self.values.remove(self.count);
        (i, a)
    }

    /// Get a reference to the value in the entry.
    pub fn get(&self) -> &T {
        &self.values[self.indices[self.count]]
    }

    /// Get a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see `into_mut`.
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.values[self.indices[self.count]]
    }

    /// Convert the `OccupiedEntry` into a mutable reference to the value in the
    /// entry with a lifetime bound to the originating `Sparse<T>` itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see `get_mut`.
    pub fn into_mut(self) -> &'a mut T {
        &mut self.values[self.indices[self.count]]
    }

    /// Set the value of the entry, and return the entry's old value.
    pub fn insert(&mut self, mut value: T) -> T {
        std::mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Take the value out of the entry, and return it.
    ///
    /// This operation is linear in time proportionate to the number of entries
    /// with index higher than the index of this entry (which is to say, it is
    /// constant time if this is the last item in the collection).
    pub fn remove(self) -> T {
        self.remove_entry().1
    }
}

/// A view into a vacant entry in a `Sparse` vector. It is part of the `Entry`
/// enum.
#[derive(Debug)]
pub struct VacantEntry<'a, T> {
    pub(super) count: usize,
    pub(super) index: usize,
    pub(super) indices: &'a mut Vec<usize>,
    pub(super) values: &'a mut Vec<T>,
    pub(super) end: &'a mut usize,
}

impl<'a, T> VacantEntry<'a, T> {
    /// Get the index that would be used when inserting a value through the
    /// `VacantEntry`.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Set the value of the entry at the `VacantEntry`'s index, and return a
    /// mutable reference to it.
    pub fn insert(self, value: T) -> &'a mut T {
        if self.index > *self.end {
            *self.end = self.index;
        }
        self.indices.insert(self.count, self.index);
        self.values.insert(self.count, value);
        &mut self.values[self.indices[self.count]]
    }
}
