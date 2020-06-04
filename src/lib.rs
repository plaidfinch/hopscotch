//! A [`hopscotch::Queue<K, V>`](struct@Queue) is a first-in-first-out queue
//! where each [`Item<K, V>`](struct@Item) in the queue has
//!
//! - a value of type `V`,
//! - an immutable tag of type `K`, and
//! - a unique `index` of type `u64` which is assigned in sequential order of
//!   insertion starting at 0 when the queue is created.
//!
//! In addition to supporting the ordinary [`push`](Queue::push),
//! [`pop`](Queue::pop), and [`get`](Queue::get) methods of a FIFO queue, a
//! hopscotch queue also supports the special, optimized methods
//! [`after`](Queue::after), [`after_mut`](Queue::after_mut),
//! [`before`](Queue::before), and [`before_mut`](Queue::before_mut).
//!
//! These methods find the next (or previous) [`Item`] (or [`ItemMut`]) in the
//! queue whose tag is equal to any of a given set of tags. For instance, the
//! signature of [`after`](Queue::after) is:
//!
//! ```
//! # use hopscotch::Item;
//! # struct X<K, V>(K, V);
//! # impl<K, V> X<K, V> {
//! pub fn after<'a, Tags>(&self, index: u64, tags: Tags) -> Option<Item<K, V>>
//!     where
//!         Tags: IntoIterator<Item = &'a K>,
//!         K: 'a,
//! # { panic!() }
//! # }
//! ```
//!
//! If we use `&[K]` for `Tags`, this signature simplifies to:
//!
//! ```
//! # use hopscotch::Item;
//! # struct X<K, V>(K, V);
//! # impl<K, V> X<K, V> {
//! pub fn after(&self, index: u64, tags: &[K]) -> Option<Item<K, V>>
//! # { panic!() }
//! # }
//! ```
//!
//! These methods are the real benefit of using a hopscotch queue over another
//! data structure. Their asymptotic time complexity is:
//!
//! - linear relative to the number of tags queried,
//! - logarithmic relative to the total number of distinct tags in the queue,
//! - constant relative to the length of the queue, and
//! - constant relative to the distance between successive items with the same
//!   tag.
//!
//! Hopscotch queues also provide flexible iterators [`Iter`]/[`IterMut`] to
//! efficiently traverse portions of their contents, sliced by index using
//! [`Iter::until`]/[`IterMut::until`] and [`Iter::after`]/[`IterMut::after`],
//! and filtered by set of desired tags using
//! [`Iter::matching_only`]/[`IterMut::matching_only`].

use rpds::RedBlackTreeMap;
use std::collections::{BTreeMap, VecDeque};
use std::convert::TryInto;
use std::iter::FromIterator;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

pub use archery::{ArcK, RcK, SharedPointerKind};

/// A hopscotch queue with keys of type `K` and items of type `V`.
///
/// **A note on pointers:** By default, queues use [`Rc`](std::rc::Rc) smart
/// pointers internally, but this prevents them from implementing [`Sync`] and
/// [`Send`], which means they cannot be sent across thread boundaries. Thanks
/// to the [`archery`](http://www.crates.io/crates/archery) crate, in contexts
/// where you want [`Queue`] to implement [`Sync`] and [`Send`], you can
/// instantiate the third type parameter `P` to [`ArcK`](archery::ArcK) instead
/// of its default value of [`RcK`](archery::RcK) (these types are re-exported
/// from `archery` for convenience). As of last benchmarking, using the
/// [`Arc`](std::sync::Arc) variant imposes an approximate 15% extra cost for
/// mutation operations ([`push`](Queue::push) and [`pop`](Queue::pop)), and
/// negligible extra cost for access operations ([`get`](Queue::get),
/// [`after`](Queue::before), [`before`](Queue::before), etc.).
#[derive(Clone)]
pub struct Queue<K: Ord, V, P: SharedPointerKind = RcK> {
    offset: u64,
    first_with_tag: BTreeMap<K, u64>,
    info: VecDeque<Info<K, P>>,
    values: VecDeque<V>,
}

/// An immutable reference to an item currently in the queue.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Item<'a, K, V> {
    index: u64,
    tag: &'a K,
    value: &'a V,
}

/// A mutable reference to an item currently in the queue.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct ItemMut<'a, K, V> {
    index: u64,
    tag: &'a K,
    value: &'a mut V,
}

/// An item that has been popped from the queue.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Popped<K, V> {
    /// The index of the item: this is unique for the entire lifetime of the
    /// queue from which this item originated.
    pub index: u64,
    /// The tag of the item which was originally assigned when the item was
    /// inserted into the queue.
    pub tag: K,
    /// The value contained in this item.
    pub value: V,
}

impl<'a, K, V> Item<'a, K, V> {
    /// The index of the item: this is unique for the entire lifetime of the
    /// queue from which this item originated.
    pub fn index(&self) -> u64 {
        self.index
    }
    /// The tag of the item which was originally assigned when the item was
    /// inserted into the queue.
    pub fn tag(&self) -> &K {
        self.tag
    }
    /// Get an immutable reference to the value contained in this item.
    pub fn value(&self) -> &'a V {
        self.value
    }
}

impl<'a, K: Ord, V> ItemMut<'a, K, V> {
    /// The index of the item: this is unique for the entire lifetime of the
    /// queue from which this item originated.
    pub fn index(&self) -> u64 {
        self.index
    }
    /// The tag of the item which was originally assigned when the item was
    /// inserted into the queue.
    pub fn tag(&self) -> &K {
        self.tag
    }
    /// Get a mutable reference to the value contained in this item.
    pub fn value_mut(&mut self) -> &mut V {
        self.value
    }
    /// Extract a mutable reference to the value whose lifetime is tied to
    /// the entire queue, not this `Item`.
    pub fn into_mut(self) -> &'a mut V {
        self.value
    }
}

impl<K: Ord, V> AsRef<V> for Item<'_, K, V> {
    fn as_ref(&self) -> &V {
        self.value
    }
}

impl<K: Ord, V> AsRef<V> for ItemMut<'_, K, V> {
    fn as_ref(&self) -> &V {
        &*self.value
    }
}

impl<K: Ord, V> AsMut<V> for ItemMut<'_, K, V> {
    fn as_mut(&mut self) -> &mut V {
        self.value
    }
}

#[derive(Debug, Clone)]
struct Info<K: Ord, P: SharedPointerKind> {
    tag: K,
    next_with_tag: usize,
    previous_with_tag: RedBlackTreeMap<K, u64, P>,
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
            let index = $index;
            let this = $self;
            // Find the item, if one exists
            let internal_index = this.as_internal_index(index)?;
            let Info{tag, ..} =
                get!(this.info,
                     internal_index
                     $(, $mutability)?)?;
            Some((& $($mutability)? this.values[internal_index], tag, index))
        }
    }
}

/// This macro implements both "before" variations: both immutable and
/// mutable. It must be a macro because while all the code is operationally the
/// same regardless of mutability, Rust does not (yet) have mutability
/// polymorphism.
macro_rules! before_impl {
    ($self:expr, $index:expr, $tags:expr $(, $mutability:tt)?) => {
        {
            let tags = $tags;
            let this = $self;
            let index = ($index).min(this.next_index().saturating_sub(1));

            let index: usize = this.as_internal_index(index)?;
            let current = this.info.get(index)?;
            let previous_index =
                tags.into_iter()
                .filter_map(|tag| Some(*current.previous_with_tag.get(tag)?))
                .max()?;
            let internal_index = this.as_internal_index(previous_index)?;
            Some((get!(this.values, internal_index $(, $mutability)?)?,
                  &this.info[internal_index].tag,
                  previous_index))
        }
    };
}

/// This macro implements both "after" variations: both immutable and
/// mutable. It must be a macro because while all the code is operationally the
/// same regardless of mutability, Rust does not (yet) have mutability
/// polymorphism.
macro_rules! after_impl {
    ($self:expr, $index:expr, $tags:expr $(, $mutability:tt)?) => {
        {
            let tags = $tags;
            let this = $self;
            let index = ($index);
            if index >= this.next_index() {
                return None;
            }
            let here_index = index.max(this.earliest_index());
            let here = this.info(here_index);

            let mut minimum: Option<u64> = None;
            if let Some(here_info) = here {
                for tag in tags {
                    if *tag == here_info.tag {
                        minimum = Some(here_index);
                        break;
                    }
                    let next_index =
                        if let Some(&previous_index) = here_info.previous_with_tag.get(tag) {
                            if let Some(info) = this.info(previous_index) {
                                previous_index.checked_add(info.next_with_tag as u64)
                            } else {
                                this.first_with_tag.get(&tag).copied()
                            }
                        } else {
                            this.first_with_tag.get(&tag).copied()
                        };
                    minimum = match (minimum, next_index) {
                        (None, Some(next_index))
                            if this.earliest_index() <= next_index => {
                                Some(next_index)
                            },
                        (Some(min), Some(next_index))
                            if this.earliest_index() <= next_index && next_index < min => {
                                Some(next_index)
                            },
                        _ => minimum,
                    }
                }
            } else {
                minimum = this.first_with_tag.values().min().copied()
            }
            // Get the item at the minimum index and return its exterior-facing
            // index and a reference to the item itself.
            let next_index = minimum?;
            let internal_index = this.as_internal_index(next_index)?;
            Some((get!(this.values, internal_index $(, $mutability)?)?,
                  &this.info[internal_index].tag,
                  next_index))
        }
    };
}

impl<K: Ord + Clone, V, P: SharedPointerKind> Queue<K, V, P> {
    /// Make a new queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = Queue::new();
    /// ```
    ///
    /// If we want to use `Arc` pointers and get thread-safety at the expense of
    /// a little performance:
    ///
    /// ```
    /// use hopscotch::{Queue, ArcK};
    ///
    /// let mut queue: Queue<usize, usize, ArcK> = Queue::new();
    /// ```
    ///
    pub fn new() -> Queue<K, V, P> {
        Self::with_capacity(0)
    }

    /// Make a new queue with a given initial allocated capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = Queue::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Queue<K, V, P> {
        Queue {
            offset: 0,
            first_with_tag: BTreeMap::new(),
            info: VecDeque::with_capacity(capacity),
            values: VecDeque::with_capacity(capacity),
        }
    }

    /// Given an external persistent index, get the current index within the
    /// internal queue that corresponds to it. This correspondence is
    /// invalidated by future changes to the queue.
    fn as_internal_index(&self, index: u64) -> Option<usize> {
        index.checked_sub(self.offset)?.try_into().ok()
    }

    /// Get the internal info at a given external index.
    fn info(&self, index: u64) -> Option<&Info<K, P>> {
        self.info.get(self.as_internal_index(index)?)
    }

    /// Get the internal info (mutably) at a given external index.
    fn info_mut(&mut self, index: u64) -> Option<&mut Info<K, P>> {
        self.info.get_mut(self.as_internal_index(index)?)
    }

    /// The number of items currently in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..4).zip(0..4).collect();
    /// assert_eq!(queue.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.info.len()
    }

    /// Returns `true` if and only if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = Queue::new();
    /// assert!(queue.is_empty());
    /// queue.push(0, 100);
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Push a new item into the queue, returning its assigned index.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, String> = Queue::new();
    /// queue.push(0, "Hello!".to_string());
    /// ```
    pub fn push(&mut self, tag: K, value: V) -> u64 {
        // The index we're about to push
        let pushed_index = self.next_index();
        let mut previous_with_tag = self
            .info
            .back()
            .map(|latest| latest.previous_with_tag.clone())
            .unwrap_or_else(RedBlackTreeMap::new_with_ptr_kind);
        // Set the next_with_tag index of the previous of this tag to point to
        // the index we're about to insert at.
        previous_with_tag.get(&tag).map(|previous_index| {
            self.info_mut(*previous_index).map(|previous_info| {
                let distance = (pushed_index - previous_index)
                    .try_into()
                    .expect("Queue invariant violation: distance greater than usize::max_value()");
                previous_info.next_with_tag = distance;
            });
        });
        // Actually insert the item into the queue
        previous_with_tag.insert_mut(tag.clone(), pushed_index);
        self.info.push_back(Info {
            tag: tag.clone(),
            previous_with_tag,
            next_with_tag: usize::max_value(),
        });
        self.values.push_back(value);
        // Make sure first_with_tag tracks this event, if it is the current
        // earliest of its tag:
        self.first_with_tag.entry(tag).or_insert(pushed_index);
        // Return the new index
        pushed_index
    }

    /// Pop an item off the back of the queue and return it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, String> = Queue::new();
    /// queue.push(42, "Hello!".to_string());
    /// let item = queue.pop()?;
    ///
    /// assert_eq!(item.index, 0);
    /// assert_eq!(item.tag, 42);
    /// assert_eq!(item.value, "Hello!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn pop(&mut self) -> Option<Popped<K, V>> {
        // The index of the thing that's about to get popped is equal to
        // the current offset, because the offset is incremented exactly
        // every time something is popped:
        let popped_index = self.offset;
        // Pop off the least recent item:
        let popped_info = self.info.pop_front()?;
        let popped_value = self.values.pop_front()?;
        // Decrement the forward distance for first_with_tag of every event tag
        // *except* the current, which should be set to the distance of the next
        // of that tag
        let next_index_with_tag = popped_index.saturating_add(popped_info.next_with_tag as u64);
        if next_index_with_tag == u64::max_value() {
            self.first_with_tag
                .remove(&popped_info.tag)
                .expect("Queue invariant violation: no first_with_tag for extant tag");
        } else {
            let earliest_index = self
                .first_with_tag
                .get_mut(&popped_info.tag)
                .expect("Queue invariant violation: no first_with_tag for extant tag");
            *earliest_index = next_index_with_tag;
        }
        // Bump the offset because we just shifted the queue
        self.offset = self.offset.checked_add(1).expect("Queue index overflow");
        // Return the pieces
        Some(Popped {
            value: popped_value,
            tag: popped_info.tag,
            index: popped_index,
        })
    }

    /// Clear the contents of the queue without de-allocating the queue's
    /// memory (though memory will still be freed for the individual elements of
    /// the queue).
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// queue.clear();
    /// assert_eq!(queue.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.first_with_tag.clear();
        self.info.clear();
        self.values.clear();
    }

    /// The index which will be assigned to the next item to be added to the
    /// queue, whenever it is added.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = Queue::new();
    /// assert_eq!(queue.next_index(), 0);
    /// let i = queue.push(0, 100);
    /// assert_eq!(i, 0);
    /// assert_eq!(queue.next_index(), 1);
    /// ```
    pub fn next_index(&self) -> u64 {
        self.offset
            .checked_add(self.len() as u64)
            .expect("Queue index overflow")
    }

    /// The earliest index which is still stored in the queue (each `pop`
    /// increments this value by 1).
    fn earliest_index(&self) -> u64 {
        self.offset
    }

    /// Get an immutable reference to the earliest item to have been inserted
    /// into the queue, which is still in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// queue.pop();
    /// assert_eq!(*queue.earliest()?.value(), 2);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn earliest(&self) -> Option<Item<K, V>> {
        self.get(self.earliest_index())
    }

    /// Get an immutable reference to the earliest item to have been inserted
    /// into the queue, which is still in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// queue.pop();
    /// *queue.earliest_mut()?.value_mut() = 500;
    /// assert_eq!(*queue.earliest()?.value(), 500);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn earliest_mut(&mut self) -> Option<ItemMut<K, V>> {
        self.get_mut(self.earliest_index())
    }

    /// Get an immutable reference to the latest item to have been inserted
    /// into the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(*queue.latest()?.value(), 9);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn latest(&self) -> Option<Item<K, V>> {
        self.get(self.next_index().saturating_sub(1))
    }

    /// Get an immutable reference to the earliest item to have been inserted
    /// into the queue, which is still in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// *queue.latest_mut()?.value_mut() = 500;
    /// assert_eq!(*queue.latest()?.value(), 500);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn latest_mut(&mut self) -> Option<ItemMut<K, V>> {
        self.get_mut(self.next_index().saturating_sub(1))
    }

    /// Returns `true` if and only if the queue contains an item whose value is
    /// equal to the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(queue.contains(&5), true);
    /// assert_eq!(queue.contains(&500), false);
    /// ```
    pub fn contains(&self, x: &V) -> bool
    where
        V: PartialEq,
    {
        self.iter().find(|i| x == i.value()).is_some()
    }

    /// Returns `true` if and only if the queue contains an item whose tag is
    /// equal to the given tag.
    ///
    /// This takes time logarithmic in the total number of tags in the queue,
    /// which is *much* faster than traversing the entire queue in search of a
    /// tag.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(queue.contains_tag(&5), true);
    /// assert_eq!(queue.contains_tag(&500), false);
    /// ```
    pub fn contains_tag(&self, t: &K) -> bool {
        self.first_with_tag.contains_key(t)
    }

    /// Get a reference to the earliest item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(*queue.get(0)?.as_ref(), 0);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the queue, even though the
    /// queue still contains items:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// assert!(queue.get(0).is_none());
    /// ```
    pub fn get(&self, index: u64) -> Option<Item<K, V>> {
        let (value, tag, index) = get_impl!(self, index)?;
        Some(Item { value, tag, index })
    }

    /// Get a mutable reference to the earliest item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), ()> { (|| {
    /// # use hopscotch::Queue;
    /// let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// let mut n = queue.get_mut(0)?;
    /// *n.as_mut() = 5000;
    /// assert_eq!(*queue.get(0)?.as_ref(), 5000);
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the queue, even though the
    /// queue still contains items:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<usize, usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// assert!(queue.get(0).is_none());
    /// ```
    pub fn get_mut(&mut self, index: u64) -> Option<ItemMut<K, V>> {
        let (value, tag, index) = get_impl!(self, index, mut)?;
        Some(ItemMut { value, tag, index })
    }

    /// Get a reference to the earliest item after or including `index` whose
    /// tag is one of those given.
    ///
    /// The `Tags` type for the list of desired tags can be anything which
    /// implements [`IntoIterator`]`<Item = &K>`. The usual choice for this is
    /// `&[K]` (as seen in the examples below), but in cases where there is an
    /// extant collection of tags, you can avoid re-allocating by passing an
    /// iterator over that same collection.
    ///
    /// # Examples
    ///
    /// Suppose we construct a queue that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    /// ```
    ///
    /// Starting from index 0, the earliest word tagged as English is "Hello"; the
    /// earliest tagged as French is "Bonjour"; the earliest tagged as either is
    /// "Hello":
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(0, &[0])?.as_ref(), "Hello");
    /// assert_eq!(queue.after(0, &[1])?.as_ref(), "Bonjour");
    /// assert_eq!(queue.after(0, &[0, 1])?.as_ref(), "Hello");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively after* index 1:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(1, &[0])?.as_ref(), "world!");
    /// assert_eq!(queue.after(1, &[1])?.as_ref(), "Bonjour");
    /// assert_eq!(queue.after(1, &[0, 1])?.as_ref(), "Bonjour");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively after* index 2:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(2, &[0])?.as_ref(), "world!");
    /// assert_eq!(queue.after(2, &[1])?.as_ref(), "le monde!");
    /// assert_eq!(queue.after(2, &[0, 1])?.as_ref(), "world!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively after* index 3:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(queue.after(3, &[0]).is_none());
    /// assert_eq!(queue.after(3, &[1])?.as_ref(), "le monde!");
    /// assert_eq!(queue.after(3, &[0, 1])?.as_ref(), "le monde!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively after* index 4:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(queue.after(4, &[0]).is_none());
    /// assert!(queue.after(4, &[1]).is_none());
    /// assert!(queue.after(4, &[0, 1]).is_none());
    /// ```
    pub fn after<'a, Tags>(&self, index: u64, tags: Tags) -> Option<Item<K, V>>
    where
        Tags: IntoIterator<Item = &'a K>,
        K: 'a,
    {
        let (value, tag, index) = after_impl!(self, index, tags)?;
        Some(Item { value, tag, index })
    }

    /// Get a mutable reference to the earliest item after or including `index`
    /// whose tag is one of those given.
    ///
    /// The `Tags` type for the list of desired tags can be anything which
    /// implements [`IntoIterator`]`<Item = &K>`. The usual choice for this is
    /// `&[K]` (as seen in the examples below), but in cases where there is an
    /// extant collection of tags, you can avoid re-allocating by passing an
    /// iterator over that same collection.
    ///
    /// This uses the same semantics for lookup as `after`: see its
    /// documentation for more examples.
    ///
    /// # Examples
    ///
    /// Suppose we construct a queue that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let beginning = 0; // same start index for both calls to `after_mut`
    /// *queue.after_mut(beginning, &[0])?.as_mut() = "Goodbye".to_string();
    /// *queue.after_mut(beginning, &[1])?.as_mut() = "Au revoir".to_string();
    ///
    /// assert_eq!(queue.get(0)?.as_ref(), "Goodbye");
    /// assert_eq!(queue.get(1)?.as_ref(), "Au revoir");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn after_mut<'a, Tags>(&mut self, index: u64, tags: Tags) -> Option<ItemMut<K, V>>
    where
        Tags: IntoIterator<Item = &'a K>,
        K: 'a,
    {
        let (value, tag, index) = after_impl!(self, index, tags, mut)?;
        Some(ItemMut { value, tag, index })
    }

    /// Get a reference to the latest item before or including `index` whose tag
    /// is one of those given.
    ///
    /// The `Tags` type for the list of desired tags can be anything which
    /// implements [`IntoIterator`]`<Item = &K>`. The usual choice for this is
    /// `&[K]` (as seen in the examples below), but in cases where there is an
    /// extant collection of tags, you can avoid re-allocating by passing an
    /// iterator over that same collection.
    ///
    /// # Examples
    ///
    /// Suppose we construct a queue that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    /// ```
    ///
    /// Starting from index 4 (which is after the end of the queue), the latest
    /// word tagged as English is "world!"; the latest tagged as French is "le
    /// monde!"; the latest tagged as either is "le monde!":
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(4, &[0])?.as_ref(), "world!");
    /// assert_eq!(queue.before(4, &[1])?.as_ref(), "le monde!");
    /// assert_eq!(queue.before(4, &[0, 1])?.as_ref(), "le monde!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively before* index 3 (the end of the queue), we get
    /// the same results as any query after the end of the queue:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(3, &[0])?.as_ref(), "world!");
    /// assert_eq!(queue.before(3, &[1])?.as_ref(), "le monde!");
    /// assert_eq!(queue.before(3, &[0, 1])?.as_ref(), "le monde!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively before* index 2:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(2, &[0])?.as_ref(), "world!");
    /// assert_eq!(queue.before(2, &[1])?.as_ref(), "Bonjour");
    /// assert_eq!(queue.before(2, &[0, 1])?.as_ref(), "world!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively before* index 1:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(1, &[0])?.as_ref(), "Hello");
    /// assert_eq!(queue.before(1, &[1])?.as_ref(), "Bonjour");
    /// assert_eq!(queue.before(1, &[0, 1])?.as_ref(), "Bonjour");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    ///
    /// Starting *inclusively before* index 0:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # fn main() -> Result<(), ()> { (|| {
    /// # let mut queue: Queue<usize, String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(0, &[0])?.as_ref(), "Hello");
    /// assert!(queue.before(0, &[1]).is_none());
    /// assert_eq!(queue.before(0, &[0, 1])?.as_ref(), "Hello");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn before<'a, Tags>(&self, index: u64, tags: Tags) -> Option<Item<K, V>>
    where
        Tags: IntoIterator<Item = &'a K>,
        K: 'a,
    {
        let (value, tag, index) = before_impl!(self, index, tags)?;
        Some(Item { value, tag, index })
    }

    /// Get a mutable reference to the latest item before or including `index`
    /// whose tag is one of those given.
    ///
    /// The `Tags` type for the list of desired tags can be anything which
    /// implements [`IntoIterator`]`<Item = &K>`. The usual choice for this is
    /// `&[K]` (as seen in the examples below), but in cases where there is an
    /// extant collection of tags, you can avoid re-allocating by passing an
    /// iterator over that same collection.
    ///
    /// This uses the same semantics for lookup as `before`: see its
    /// documentation for more examples.
    ///
    /// # Examples
    ///
    /// Suppose we construct a queue that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// # fn main() -> Result<(), ()> { (|| {
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let end = 5; // same end index for both calls to `after_mut`
    /// *queue.before_mut(end, &[0])?.as_mut() = "my friends!".to_string();
    /// *queue.before_mut(end, &[1])?.as_mut() = "mes amis!".to_string();
    ///
    /// assert_eq!(queue.get(2)?.as_ref(), "my friends!");
    /// assert_eq!(queue.get(3)?.as_ref(), "mes amis!");
    /// # Some(()) })().map_or_else(|| Err(()), Ok) }
    /// ```
    pub fn before_mut<'a, Tags>(&mut self, index: u64, tags: Tags) -> Option<ItemMut<K, V>>
    where
        Tags: IntoIterator<Item = &'a K>,
        K: 'a,
    {
        let (value, tag, index) = before_impl!(self, index, tags, mut)?;
        Some(ItemMut { value, tag, index })
    }

    /// Shrink the memory used by the queues in this queue as much as possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, ()> = Queue::new();
    /// for _ in 0 .. 10_000 {
    ///     queue.push(0, ());
    /// }
    /// for _ in 0 .. 10_000 {
    ///     queue.pop();
    /// }
    /// queue.shrink_to_fit();
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.info.shrink_to_fit();
        self.values.shrink_to_fit();
    }

    /// Get an iterator of immutable items currently in the queue, in insertion
    /// order from earliest to latest.
    ///
    /// This iterator can be further restricted using its
    /// [`after`](Iter::after), [`until`](Iter::until), and
    /// [`matching_only`](Iter::matching_only) methods to start at a given
    /// index, terminate at a given index, and return only certain tags,
    /// respectively.
    ///
    /// The returned iterator is double-ended, and therefore can be traversed in
    /// reverse order using the [`.rev()`](Iterator::rev) method.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let english: Vec<&str> =
    ///     queue
    ///     .iter()
    ///     .matching_only(&[0])
    ///     .map(|i| i.value().as_ref()).collect();
    /// assert_eq!(english, &["Hello", "world!"]);
    ///
    /// let all_backwards: Vec<&str> =
    ///     queue.iter().rev() // <-- notice the reversal
    ///     .map(|i| i.value().as_ref()).collect();
    /// assert_eq!(all_backwards, &["le monde!", "world!", "Bonjour", "Hello"]);
    /// ```
    pub fn iter(&self) -> Iter<K, V, impl Iterator<Item = &'_ K> + Clone, P> {
        let head = Some(self.next_index().saturating_sub(1));
        let tail = Some(self.earliest_index());
        Iter {
            inner: self,
            tags: None::<std::iter::Empty<&'_ K>>,
            head,
            tail,
        }
    }

    /// Get an iterator of mutable items currently in the queue, in insertion
    /// order from earliest to latest.
    ///
    /// This iterator can be further restricted using its
    /// [`after`](IterMut::after), [`until`](IterMut::until), and
    /// [`matching_only`](IterMut::matching_only) methods to start at a given
    /// index, terminate at a given index, and return only certain tags,
    /// respectively.
    ///
    /// The returned iterator is double-ended, and therefore can be traversed in
    /// reverse order using the [`.rev()`](Iterator::rev) method.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// for mut item in queue.iter_mut().matching_only(&[0]) {
    ///    *item.as_mut() = item.as_mut().to_uppercase();
    /// }
    ///
    /// let words: Vec<&str> =
    ///     queue.iter()
    ///     .map(|i| i.value().as_ref()).collect();
    /// assert_eq!(words, &["HELLO", "Bonjour", "WORLD!", "le monde!"]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V, impl Iterator<Item = &'_ K> + Clone, P> {
        let head = Some(self.next_index().saturating_sub(1));
        let tail = Some(self.earliest_index());
        IterMut {
            inner: self,
            tags: None::<std::iter::Empty<&'_ K>>,
            head,
            tail,
        }
    }
}

impl<K: Ord + Clone, V, P: SharedPointerKind> FromIterator<(K, V)> for Queue<K, V, P> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let iter = iter.into_iter();
        let mut queue = Queue::with_capacity(iter.size_hint().0);
        for (tag, item) in iter {
            queue.push(tag, item);
        }
        queue
    }
}

impl<K: Ord + Clone, V, P: SharedPointerKind> Extend<(K, V)> for Queue<K, V, P> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        for (tag, item) in iter {
            self.push(tag, item);
        }
    }
}

/// An iterator over immutable references to items in a queue. Created by
/// [`Queue::iter`].
#[derive(Clone)]
pub struct Iter<'a, 'b, K, V, Tags, P = RcK>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    inner: &'a Queue<K, V, P>,
    tags: Option<Tags>,
    head: Option<u64>,
    tail: Option<u64>,
}

impl<'a, 'b, K, V, T, P> Iter<'a, 'b, K, V, T, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    T: Iterator<Item = &'b K> + Clone,
{
    /// Restrict this iterator to indices greater than or equal to `earliest`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let queue: Queue<usize, usize> = (0..=3).zip(0..=3).collect();
    /// let vec: Vec<_> = queue.iter().after(2).map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[2, 3]);
    /// ```
    pub fn after(self, earliest: u64) -> Iter<'a, 'b, K, V, T, P> {
        Iter {
            inner: self.inner,
            tags: self.tags,
            head: self.head,
            tail: self.tail.map(|t| t.max(earliest)),
        }
    }

    /// Restrict this iterator to indices less than or equal to `latest`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let queue: Queue<usize, usize> = (0..=3).zip(0..=3).collect();
    /// let vec: Vec<_> = queue.iter().until(1).map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[0, 1]);
    /// ```
    pub fn until(self, latest: u64) -> Iter<'a, 'b, K, V, T, P> {
        Iter {
            inner: self.inner,
            tags: self.tags,
            head: self.head.map(|h| h.min(latest)),
            tail: self.tail,
        }
    }

    /// Restrict this iterator to tags in the given list of tags.
    ///
    /// This results in the same efficiency characteristics as the
    /// [`Queue::before`] and [`Queue::after`] methods: each item is produced in
    /// constant time relative to the distance between matching tags.
    ///
    ///  If `matching_only` is called twice, the set of tags given in the second
    ///  call completely overrides those given in the first.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let queue: Queue<usize, usize> =
    ///     [0, 1, 0, 1].iter().copied().zip(0..=3).collect();
    /// let vec: Vec<_> =
    ///     queue.iter().matching_only(&[1]).map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[1, 3]);
    /// ```
    pub fn matching_only<Tags>(self, tags: Tags) -> Iter<'a, 'b, K, V, Tags::IntoIter, P>
    where
        Tags: IntoIterator<Item = &'b K>,
        Tags::IntoIter: Clone,
    {
        Iter {
            inner: self.inner,
            tags: Some(tags.into_iter()),
            head: self.head,
            tail: self.tail,
        }
    }
}

impl<'a, 'b, K, V, Tags, P> Iterator for Iter<'a, 'b, K, V, Tags, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    type Item = Item<'a, K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags.clone() {
            self.inner.after(self.tail?, tags)
        } else {
            self.inner.get(self.tail?)
        }?;
        self.tail = item.index.checked_add(1);
        if item.index > self.head? {
            return None;
        }
        Some(item)
    }
}

impl<'a, 'b, K, V, Tags, P> DoubleEndedIterator for Iter<'a, 'b, K, V, Tags, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags.clone() {
            self.inner.before(self.head?, tags)
        } else {
            self.inner.get(self.head?)
        }?;
        self.head = item.index.checked_sub(1);
        if item.index < self.tail? {
            return None;
        }
        Some(item)
    }
}

/// An iterator over mutable references to items in a queue. Created by
/// [`Queue::iter_mut`].
pub struct IterMut<'a, 'b, K, V, Tags, P = RcK>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    inner: &'a mut Queue<K, V, P>,
    tags: Option<Tags>,
    head: Option<u64>,
    tail: Option<u64>,
}

impl<'a, 'b, K, V, T, P> IterMut<'a, 'b, K, V, T, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    T: Iterator<Item = &'b K> + Clone,
{
    /// Restrict this iterator to indices greater than or equal to `earliest`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..=3).zip(0..=3).collect();
    /// for mut item in queue.iter_mut().after(2) {
    ///    *item.value_mut() *= 1000;
    /// }
    /// let vec: Vec<_> = queue.iter().map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[0, 1, 2000, 3000]);
    /// ```
    pub fn after(self, earliest: u64) -> IterMut<'a, 'b, K, V, T, P> {
        IterMut {
            inner: self.inner,
            tags: self.tags,
            head: self.head,
            tail: self.tail.map(|t| t.max(earliest)),
        }
    }

    /// Restrict this iterator to indices less than or equal to `latest`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> = (0..=3).zip(0..=3).collect();
    /// for mut item in queue.iter_mut().until(1) {
    ///    *item.value_mut() += 1000;
    /// }
    /// let vec: Vec<_> = queue.iter().map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[1000, 1001, 2, 3]);
    /// ```
    pub fn until(self, latest: u64) -> IterMut<'a, 'b, K, V, T, P> {
        IterMut {
            inner: self.inner,
            tags: self.tags,
            head: self.head.map(|h| h.min(latest)),
            tail: self.tail,
        }
    }

    /// Restrict this iterator to tags in the given list of tags.
    ///
    /// This results in the same efficiency characteristics as the
    /// [`Queue::before`] and [`Queue::after`] methods: each item is produced in
    /// constant time relative to the distance between matching tags.
    ///
    ///  If `matching_only` is called twice, the set of tags given in the second
    ///  call completely overrides those given in the first.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize, usize> =
    ///     [0, 1, 0, 1].iter().copied().zip(0..=3).collect();
    /// for mut item in queue.iter_mut().matching_only(&[1]) {
    ///    *item.value_mut() *= 1000;
    /// }
    /// let vec: Vec<_> = queue.iter().map(|i| *i.value()).collect();
    /// assert_eq!(&vec, &[0, 1000, 2, 3000]);
    /// ```
    pub fn matching_only<Tags>(self, tags: Tags) -> IterMut<'a, 'b, K, V, Tags::IntoIter, P>
    where
        Tags: IntoIterator<Item = &'b K>,
        Tags::IntoIter: Clone,
    {
        IterMut {
            inner: self.inner,
            tags: Some(tags.into_iter()),
            head: self.head,
            tail: self.tail,
        }
    }
}

// A note on unsafe blocks below: the potential unsafety here would result from
// accidentally aliasing two mutable pointers. This is not possible, because the
// index is always incremented by at least one, which means we'll never produce
// the same thing again -- even in the DoubleEndedIterator case.

impl<'a, 'b, K, V, Tags, P> Iterator for IterMut<'a, 'b, K, V, Tags, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    type Item = ItemMut<'a, K, V>;

    fn next(&'_ mut self) -> Option<ItemMut<'a, K, V>> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags.clone() {
            self.inner.after_mut(self.tail?, tags)
        } else {
            self.inner.get_mut(self.tail?)
        }?;
        self.tail = item.index.checked_add(1);
        if item.index > self.head? {
            return None;
        }
        Some(ItemMut {
            value: unsafe { &mut *(item.value as *mut _) },
            index: item.index,
            tag: unsafe { &*(item.tag as *const _) },
        })
    }
}

impl<'a, 'b, K, V, Tags, P> DoubleEndedIterator for IterMut<'a, 'b, K, V, Tags, P>
where
    P: SharedPointerKind,
    K: Ord + Clone + 'b,
    Tags: Iterator<Item = &'b K> + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags.clone() {
            self.inner.before_mut(self.head?, tags)
        } else {
            self.inner.get_mut(self.head?)
        }?;
        self.head = item.index.checked_sub(1);
        if item.index < self.tail? {
            return None;
        }
        Some(ItemMut {
            value: unsafe { &mut *(item.value as *mut _) },
            index: item.index,
            tag: unsafe { &*(item.tag as *const _) },
        })
    }
}

// Implementing various standard traits for Queues:

impl<K: Clone + Ord + Debug, V: Debug, P: SharedPointerKind> Debug for Queue<K, V, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K: Clone + Ord + PartialEq, V: PartialEq, P: SharedPointerKind> PartialEq for Queue<K, V, P> {
    fn eq(&self, other: &Queue<K, V, P>) -> bool {
        self.offset == other.offset
            && self.info.iter().zip(other.info.iter()).all(|(i, j)| i.tag == j.tag)
            && self.values == other.values
    }

    fn ne(&self, other: &Queue<K, V, P>) -> bool {
        self.offset != other.offset
            || self.info.iter().zip(other.info.iter()).any(|(i, j)| i.tag != j.tag)
            || self.values != other.values
    }
}

impl<K: Clone + Ord + Eq, V: Eq, P: SharedPointerKind> Eq for Queue<K, V, P> {
    // No implementation necessary.
}

impl<K: Clone + Ord, V: PartialOrd, P: SharedPointerKind> PartialOrd for Queue<K, V, P> {
    fn partial_cmp(&self, other: &Queue<K, V, P>) -> Option<std::cmp::Ordering> {
        match self.offset.partial_cmp(&other.offset)? {
            std::cmp::Ordering::Equal => {
                let self_tags = self.info.iter().map(|i| &i.tag);
                let other_tags = other.info.iter().map(|i| &i.tag);
                match self_tags.partial_cmp(other_tags)? {
                    std::cmp::Ordering::Equal =>
                        self.values.iter().partial_cmp(other.values.iter()),
                    other => Some(other),
                }
            },
            other => Some(other),
        }
    }
}

impl<K: Clone + Ord, V: Ord, P: SharedPointerKind> Ord for Queue<K, V, P> {
    fn cmp(&self, other: &Queue<K, V, P>) -> std::cmp::Ordering {
        match self.offset.cmp(&other.offset) {
            std::cmp::Ordering::Equal => {
                let self_tags = self.info.iter().map(|i| &i.tag);
                let other_tags = other.info.iter().map(|i| &i.tag);
                match self_tags.cmp(other_tags) {
                    std::cmp::Ordering::Equal =>
                        self.values.iter().cmp(other.values.iter()),
                    other => other,
                }
            },
            other => other,
        }
    }
}

impl<K: Clone + Ord, V, P: SharedPointerKind> std::default::Default for Queue<K, V, P> {
    fn default() -> Queue<K, V, P> {
        Queue::new()
    }
}

impl<K: Clone + Ord + Hash, V: Hash, P: SharedPointerKind> Hash for Queue<K, V, P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.offset.hash(state);
        self.info.iter().for_each(|i| i.tag.hash(state));
        self.values.iter().for_each(|v| v.hash(state));
    }
}
