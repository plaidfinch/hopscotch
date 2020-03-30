use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::iter::FromIterator;

pub mod sparse;
use sparse::Sparse;

// TODO: implement get_before(_mut) and forward/reverse iterators
// TODO: full simulation testing
// TODO: benchmark
// TODO: parameterize over the type of sparse collection?

/// A `TaggedBuffer` is a first-in-first-out (FIFO) queue where each item in the
/// queue is additionally associated with an immutable *tag* of type `usize` and
/// a uniquely assigned sequential *index* of type `u64`. Unlike in a queue like
/// `VecDeque`, queue operations *do not* change the `index` of items; the index
/// is fixed from the time of the item's insertion to its removal, and each new
/// inserted item is given an index one greater than that inserted before it.
///
/// In addition to supporting the ordinary `push`, `pop`, and `get` methods of a
/// FIFO queue, a `TaggedBuffer` supports the methods `get_after` and `get_after`
/// (and their respective `mut` variants), which query the queue to determine
/// the next item in the queue whose `tag` is any of a given set of tags. These
/// methods run in linear time relative to the number of tags queried,
/// logarithmic time relative to the total number of distinct tags in the queue,
/// and constant time relative to the size of the queue and the distance between
/// successive items of the same tag.
///
/// This data structure performs best and uses the least memory when the set of
/// tags is small and mostly unchanging across the lifetime of the buffer. A
/// given buffer may use memory proportionate to the product of its length and
/// the number of distinct tags within it.
#[derive(Debug, Clone)]
pub struct TaggedBuffer<T> {
    offset: u64,
    first_with_tag: Sparse<usize>,
    queue: VecDeque<InternalItem<T>>,
}

/// An item from the buffer, either one that is currently in it, or one that has
/// been removed, e.g. by `pop()`. For a buffer of values of type `T`, different
/// methods will return `Item<T>`, `Item<&T>` and `Item<&mut T>`, as appropriate
/// to the borrowing properties of that method.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Item<T> {
    /// The index of the item: this is unique for the entire lifetime of the
    /// buffer from which this item originated.
    pub index: u64,
    /// The tag of the item which was originally assigned when the item was
    /// inserted into the buffer.
    pub tag: usize,
    /// The item itself (or a reference to one, i.e. `&T`, or `&mut T`).
    pub value: T,
}

#[derive(Debug, Clone)]
struct InternalItem<T> {
    value: T,
    next_with_tag: usize,
    previous_with_tag: Sparse<usize>,
}

impl<T> InternalItem<T> {
    fn has_tag(&self, tag: usize) -> bool {
        if let Some(0) = self.previous_with_tag.get(tag) {
            true
        } else {
            false
        }
    }
}

/// Either e.get(i), or e.get_mut(i), depending on whether a third argument is
/// supplied that is "mut".
macro_rules! get {
    ($e:expr, $i:expr) => {
        $e.get($i)
    };
    ($e:expr, $i:expr, mut) => {
        $e.get_mut($i)
    };
}

/// This macro implements both exact "get" versions: mutable and immutable. We
/// need to use a macro because Rust does not yet have mutability polymorphism.
macro_rules! get_impl {
    ($self:expr, $index:expr $(, $mutability:tt)?) => {
        {
            // Find the item, if one exists
            let InternalItem {
                previous_with_tag,
                value, ..
            } = get!($self.queue,
                    $index.checked_sub($self.offset)?.try_into().ok()?
                    $(, $mutability)?)?;
            // Determine the tag of the item
            let mut tag = None;
            for (t, d) in previous_with_tag {
                if *d == 0 {
                    tag = Some(t);
                    break;
                }
            }
            Some(Item {
                value,
                index: $index,
                tag: tag.expect("No 0 element in get_exact item"),
            })
        }
    }
}

/// This macro implements all four "get" variations: both immutable and mutable,
/// and exclusively-after and here-or-after. It must be a macro because while
/// all the code is operationally the same regardless of mutability, Rust does
/// not (yet) have mutability polymorphism.
macro_rules! get_after_impl {
    ($self:expr, $index:expr, $tags:expr $(, $mutability:tt)?) => {
        {
            let index = $index;
            let (next_index_tag, next_index): (usize, usize) =
                if let Some(index) = index.checked_sub($self.offset) {
                    // If the index given refers to an event after the start of
                    // the event buffer at present...
                    let index = index.try_into().ok()?;
                    let current = $self.queue.get(index)?;
                    $tags.iter().copied().map(|tag| {
                        (tag, if current.has_tag(tag) {
                            index
                        } else {
                            // Get the distance backwards to the previous of
                            // this tag.
                            let distance = current.previous_with_tag.get(tag)
                                .unwrap_or(&usize::max_value());
                            // Get the index of the previous of this tag
                            if let Some(previous_index) = index.checked_sub(*distance) {
                                // If index is >= 0, then find index of the next
                                // of tag. This will be ahead of the current
                                // index, because next_k(previous_k(current_k'))
                                // where k != k' can't lie before current_k' or
                                // else previous_k should have been next_k, a
                                // contradiction.
                                $self.queue.get(previous_index)
                                    .map_or(usize::max_value(), |item| {
                                        index.saturating_add(
                                            item.next_with_tag.checked_sub(1)
                                                .expect("next_with_tag field should never be zero")
                                        )})
                            } else {
                                // If previous_index is < 0, then find index of
                                // the first of this tag. This case happens when
                                // there were no preceding events of the
                                // particular tag, but there might be ones in
                                // the future of it.
                                *$self.first_with_tag.get(tag)
                                    .unwrap_or(&usize::max_value())
                            }
                        })
                    }).min_by_key(|(_, i)| i.clone())?
                } else {
                    // If the index requested lies before the buffer, pick whichever
                    // event in the set of tags happened first in the buffer
                    $tags.iter().copied()
                        .filter_map(|tag| Some((tag, *$self.first_with_tag.get(tag)?)))
                        .min_by_key(|(_, i)| i.clone())?
                };
            // Get the item at the minimum index and return its exterior-facing
            // index and a reference to the item itself.
            let item = get!($self.queue, next_index $(, $mutability)?)?;
            Some(Item {
                value: & $($mutability)? item.value,
                tag: next_index_tag,
                index: (next_index as u64).checked_add($self.offset)
                    .expect("Buffer index overflow")
            })
        }
    };
}

impl<T> TaggedBuffer<T> {
    /// Make a new buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = TaggedBuffer::new();
    /// ```
    pub fn new() -> TaggedBuffer<T> {
        Self::with_capacity(0)
    }

    /// Make a new buffer with a given initial allocated capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = TaggedBuffer::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> TaggedBuffer<T> {
        TaggedBuffer {
            offset: 0,
            first_with_tag: Sparse::new(),
            queue: VecDeque::with_capacity(capacity),
        }
    }

    /// The number of items currently in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = (0..4).zip(0..4).collect();
    /// assert_eq!(buffer.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    /// The index which will be assigned to the next item to be added to the
    /// buffer, whenever it is added.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = TaggedBuffer::new();
    /// assert_eq!(buffer.next_index(), 0);
    /// let i = buffer.push(0, 100);
    /// assert_eq!(i, 0);
    /// assert_eq!(buffer.next_index(), 1);
    /// ```
    pub fn next_index(&self) -> u64 {
        self.offset
            .checked_add(self.queue.len() as u64)
            .expect("Buffer index overflow")
    }

    /// The first index which is still stored in the buffer (each `pop`
    /// increments this value by 1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// buffer.pop();
    /// buffer.pop();
    /// assert_eq!(buffer.first_index(), 2);
    /// ```
    pub fn first_index(&self) -> u64 {
        self.offset
    }

    /// Clear the contents of the buffer without de-allocating the queue's
    /// memory (though memory will still be freed for the individual elements of
    /// the queue).
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// buffer.clear();
    /// assert_eq!(buffer.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.first_with_tag.clear();
        self.queue.clear();
    }

    /// Get a reference to the first item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(*buffer.get(0).unwrap().value, 0);
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the buffer, even though the
    /// buffer still contains items:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// buffer.pop();
    /// assert!(buffer.get(0).is_none());
    /// ```
    pub fn get(&self, index: u64) -> Option<Item<&T>> {
        get_impl!(self, index)
    }

    /// Get a mutable reference to the first item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// let mut n = buffer.get_mut(0).unwrap().value;
    /// *n = 5000;
    /// assert_eq!(*buffer.get(0).unwrap().value, 5000);
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the buffer, even though the
    /// buffer still contains items:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<usize> = (0..10).zip(0..10).collect();
    /// buffer.pop();
    /// assert!(buffer.get(0).is_none());
    /// ```
    pub fn get_mut(&mut self, index: u64) -> Option<Item<&mut T>> {
        get_impl!(self, index, mut)
    }

    /// Get a reference to the first item after or including `index` whose tag
    /// is one of those given.
    ///
    /// # Examples
    ///
    /// Suppose we construct a buffer that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    /// ```
    ///
    /// Starting from index 0, the first word tagged as English is "Hello"; the
    /// first tagged as French is "Bonjour"; the first tagged as either is
    /// "Hello":
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(buffer.get_after(0, &[0]).unwrap().value, "Hello");
    /// assert_eq!(buffer.get_after(0, &[1]).unwrap().value, "Bonjour");
    /// assert_eq!(buffer.get_after(0, &[0, 1]).unwrap().value, "Hello");
    /// ```
    ///
    /// Starting *inclusively from* index 1:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(buffer.get_after(1, &[0]).unwrap().value, "world!");
    /// assert_eq!(buffer.get_after(1, &[1]).unwrap().value, "Bonjour");
    /// assert_eq!(buffer.get_after(1, &[0, 1]).unwrap().value, "Bonjour");
    /// ```
    ///
    /// Starting *inclusively from* index 2:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(buffer.get_after(2, &[0]).unwrap().value, "world!");
    /// assert_eq!(buffer.get_after(2, &[1]).unwrap().value, "le monde!");
    /// assert_eq!(buffer.get_after(2, &[0, 1]).unwrap().value, "world!");
    /// ```
    ///
    /// Starting *inclusively from* index 3:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(buffer.get_after(3, &[0]).is_none());
    /// assert_eq!(buffer.get_after(3, &[1]).unwrap().value, "le monde!");
    /// assert_eq!(buffer.get_after(3, &[0, 1]).unwrap().value, "le monde!");
    /// ```
    ///
    /// Starting *inclusively from* index 4:
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// # let mut buffer: TaggedBuffer<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(buffer.get_after(4, &[0]).is_none());
    /// assert!(buffer.get_after(4, &[1]).is_none());
    /// assert!(buffer.get_after(4, &[0, 1]).is_none());
    /// ```
    pub fn get_after(&self, index: u64, tags: &[usize]) -> Option<Item<&T>> {
        get_after_impl!(self, index, tags)
    }

    /// Get a mutable reference to the first item after or including `index`
    /// whose tag is one of those given.
    ///
    /// This uses the same semantics for lookup as `get_after`: see its
    /// documentation for more examples.
    ///
    /// # Examples
    ///
    /// Suppose we construct a buffer that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let beginning = 0; // same start index for both calls to `get_after_mut`
    /// *buffer.get_after_mut(beginning, &[0]).unwrap().value = "Goodbye".to_string();
    /// *buffer.get_after_mut(beginning, &[1]).unwrap().value = "Au revoir".to_string();
    ///
    /// assert_eq!(buffer.get(0).unwrap().value, "Goodbye");
    /// assert_eq!(buffer.get(1).unwrap().value, "Au revoir");
    /// ```
    pub fn get_after_mut(&mut self, index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
        get_after_impl!(self, index, tags, mut)
    }

    /// Pop an item off the back of the buffer and return it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<String> = TaggedBuffer::new();
    /// buffer.push(42, "Hello!".to_string());
    /// let item = buffer.pop().unwrap();
    ///
    /// assert_eq!(item.index, 0);
    /// assert_eq!(item.tag, 42);
    /// assert_eq!(item.value, "Hello!");
    /// ```
    pub fn pop(&mut self) -> Option<Item<T>> {
        Some(self.pop_and_reclaim()?.0)
    }

    /// Pop an item off the buffer and reclaim the memory it used, so we can
    /// avoid needless allocations. This is an internal-only function.
    fn pop_and_reclaim(&mut self) -> Option<(Item<T>, Sparse<usize>)> {
        // The index of the thing that's about to get popped is equal to
        // the current offset, because the offset is incremented exactly
        // every time something is popped:
        let popped_index = self.offset;
        // Pop off the least recent item:
        let mut popped = self.queue.pop_front()?;
        // Decrement the forward distance for first_with_tag of every
        // event tag *except* the current
        let mut popped_tag = None;
        let first_with_tag_len = self.first_with_tag.len();
        let queue_len = self.queue.len();
        self.first_with_tag.retain(|k, dist| {
            if popped.has_tag(k) {
                *dist = popped.next_with_tag;
                popped_tag = Some(k);
            }
            // It's safe to .unwrap() below because:
            // - if popped.has_tag(k), then *dist = popped.next_with_tag
            //   and popped.next_with_tag > 0, because this invariant
            //   always holds for next_with_tag
            // - if !popped.has_tag(k), then *dist > 0 because *dist
            //   should always hold the index of the thing with tag k,
            //   and we know that the thing at index 0 is not with tag k
            if *dist < queue_len {
                *dist = dist.checked_sub(1).expect("Zero in wrong place in first_with_tag");
                true // keep this thing
            } else {
                false // drop this thing
            }
        });
        // Shrink the first_with_tag vector if necessary
        if first_with_tag_len != self.first_with_tag.len() {
            self.first_with_tag.shrink_to_fit();
        }
        // Clear the vec but retain its memory
        popped.previous_with_tag.clear();
        // Bump the offset because we just shifted the queue
        self.offset = self.offset.checked_add(1).expect("Buffer index overflow");
        // Return the pieces
        Some((
            Item {
                value: popped.value,
                tag: popped_tag.expect("No 0 element in popped item"),
                index: popped_index,
            },
            popped.previous_with_tag,
        ))
    }

    /// Push a new item into the buffer, returning its assigned index.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<String> = TaggedBuffer::new();
    /// buffer.push(0, "Hello!".to_string());
    /// ```
    pub fn push(&mut self, tag: usize, value: T) -> u64 {
        self.push_and_maybe_pop(tag, value, false).0
    }

    /// Push a new item into the buffer, evicting the least recent item from the
    /// buffer at the same time, and returning that old item, if one existed.
    /// This is equivalent to calling `pop` and then `push`, but is more
    /// efficient because it saves allocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use event_queue_demo::TaggedBuffer;
    /// let mut buffer: TaggedBuffer<String> = TaggedBuffer::new();
    /// buffer.push(42, "Hello!".to_string());
    /// let (new_index, popped) = buffer.push_and_pop(1, "Goodbye!".to_string());
    /// let item = popped.unwrap();
    ///
    /// assert_eq!(new_index, 1);
    /// assert_eq!(item.index, 0);
    /// assert_eq!(item.tag, 42);
    /// assert_eq!(item.value, "Hello!");
    /// ```
    pub fn push_and_pop(&mut self, tag: usize, value: T) -> (u64, Option<Item<T>>) {
        self.push_and_maybe_pop(tag, value, true)
    }

    /// Push a new item into the buffer, potentially evicting an old item if the
    /// buffer is full. Returns the index of the newly pushed item paired with
    /// the old item and its own index, if an old item was evicted.
    fn push_and_maybe_pop(
        &mut self,
        tag: usize,
        value: T,
        also_pop: bool,
    ) -> (u64, Option<Item<T>>) {
        // Calculate the backward distance to the previous of this tag.
        let distance_to_previous = self
            .queue
            .back()
            .and_then(|latest| latest.previous_with_tag.get(tag).copied())
            .unwrap_or(usize::max_value())
            .saturating_add(1);
        // Find the previous of this tag, if any, and set its next_with_tag
        // pointer to point to this new item
        self.queue
            .len()
            .checked_sub(distance_to_previous)
            .and_then(|i| self.queue.get_mut(i))
            .map(|item| item.next_with_tag = distance_to_previous);
        // Get a fresh vector for tracking the distance to all previous events,
        // either by reclaiming memory of the least recent event (if directed to
        // pop) or by allocating a new one.
        let (popped_item, mut previous_with_tag) = if also_pop {
            if let Some((item, vec)) = self.pop_and_reclaim() {
                (Some(item), vec)
            } else {
                (None, Sparse::new())
            }
        } else {
            (None, Sparse::new())
        };
        // Populate the vector with the relative backward distances to the
        // previous events of each tag.
        if let Some(latest) = self.queue.back() {
            let mut tag_inserted = false;
            for (t, dist) in latest.previous_with_tag.iter() {
                match t.cmp(&tag) {
                    Ordering::Less => {
                        if *dist < self.queue.len() {
                            previous_with_tag.entry(t).insert(dist.saturating_add(1));
                        }
                    }
                    Ordering::Equal => {
                        previous_with_tag.entry(t).insert(0);
                        tag_inserted = true;
                    }
                    Ordering::Greater => {
                        if !tag_inserted {
                            previous_with_tag.entry(tag).insert(0);
                            tag_inserted = true;
                        }
                        if *dist < self.queue.len() {
                            previous_with_tag.entry(t).insert(dist.saturating_add(1));
                        }
                    }
                }
            }
            if !tag_inserted {
                previous_with_tag.entry(tag).insert(0);
                // tag_inserted = true;
            }
        } else {
            previous_with_tag.entry(tag).insert(0);
        }
        // Free memory from the given vec that isn't necessary anymore
        previous_with_tag.shrink_to_fit();
        // Actually insert the item into the queue
        self.queue.push_back(InternalItem {
            value,
            next_with_tag: usize::max_value(),
            previous_with_tag,
        });
        // Make sure first_with_tag tracks this event, if it is the current
        // first of its tag:
        if self.first_with_tag.get(tag).is_none() {
            self.first_with_tag.entry(tag).insert(self.queue.len() - 1);
        }
        // Calculate the index of the just-inserted thing
        (self.offset
         .checked_add(self.queue.len() as u64)
         .expect("Buffer index overflow") - 1,
         popped_item)
    }
}

impl<T> FromIterator<(usize, T)> for TaggedBuffer<T> {
    fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item = (usize, T)> {
        let iter = iter.into_iter();
        let mut buffer = TaggedBuffer::with_capacity(iter.size_hint().0);
        for (tag, item) in iter {
            buffer.push(tag, item);
        }
        buffer
    }
}

impl<T: std::fmt::Display> std::fmt::Display for TaggedBuffer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let max_spaces = format!(
            "{}",
            self.first_with_tag
                .values()
                .filter(|x| **x != usize::max_value())
                .max()
                .unwrap_or(&0)
                .max(
                    &self
                        .queue
                        .iter()
                        .map(|i| {
                            (if i.next_with_tag == usize::max_value() {
                                0
                            } else {
                                i.next_with_tag
                            })
                            .max(
                                *i.previous_with_tag
                                    .values()
                                    .filter(|x| **x != usize::max_value())
                                    .max()
                                    .unwrap_or(&0),
                            )
                        })
                        .max()
                        .unwrap_or(0)
                )
        )
        .len();
        let max_width = self
            .queue
            .iter()
            .map(|i| i.previous_with_tag.len())
            .max()
            .unwrap_or(0);
        let spaces = |f: &mut std::fmt::Formatter, s: String| {
            write!(f, "{}", s)?;
            for _ in 0..max_spaces.saturating_sub(s.len()) {
                write!(f, "   ")?
            }
            Ok(())
        };
        let dist = |n: usize| {
            if n != usize::max_value() {
                format!("{}", n)
            } else {
                "∞".to_string()
            }
        };
        for _ in 0..max_width {
            write!(f, " ")?;
            spaces(f, " ↱ ".to_string())?;
        }
        write!(f, " →")?;
        for t in 0..max_width {
            if let Some(d) = self.first_with_tag.get(t) {
                write!(f, " ")?;
                spaces(f, format!(" ↓{}", dist(*d)))?;
            } else {
                write!(f, " ")?;
                spaces(f, format!("  "))?;
            }
        }
        for i in &self.queue {
            write!(f, "\n")?;
            for t in 0..max_width {
                if let Some(d) = i.previous_with_tag.get(t) {
                    if *d > 0 {
                        write!(f, " ")?;
                        spaces(f, format!(" ↑{}", dist(*d)))?;
                    } else {
                        spaces(f, format!(" ({})", t))?;
                    }
                } else {
                    write!(f, " ")?;
                    spaces(f, "".to_string())?;
                }
            }
            write!(f, " |")?;
            for t in 0..max_width {
                if let Some(d) = i.previous_with_tag.get(t) {
                    if *d == 0 {
                        write!(f, " ")?;
                        spaces(f, format!(" ↓{}", dist(i.next_with_tag)))?;
                    } else {
                        spaces(f, "  ⋮ ".to_string())?;
                    }
                } else {
                    spaces(f, "  ⋮ ".to_string())?;
                }
            }
            write!(f, " | {}", i.value)?
        }
        Ok(())
    }
}
