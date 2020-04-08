use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::iter::FromIterator;

use im::hashmap::{HashMap, Entry};

/// A `Queue` is a first-in-first-out (FIFO) queue where each item in the
/// queue is additionally associated with an immutable *tag* of type `usize` and
/// a uniquely assigned sequential *index* of type `u64`. Unlike in a queue like
/// `VecDeque`, queue operations *do not* change the `index` of items; the index
/// is fixed from the time of the item's insertion to its removal, and each new
/// inserted item is given an index one greater than that inserted before it.
///
/// In addition to supporting the ordinary `push`, `pop`, and `get` methods of a
/// FIFO queue, a `Queue` supports the methods `after` and `before` (and their
/// respective `mut` variants), which query the queue to determine the next item
/// in the queue whose `tag` is any of a given set of tags. These methods run in
/// linear time relative to the number of tags queried, logarithmic time
/// relative to the total number of distinct tags in the queue, and constant
/// time relative to the size of the queue and the distance between successive
/// items of the same tag.
///
/// This data structure performs best and uses the least memory when the set of
/// tags is small and mostly unchanging across the lifetime of the queue. A
/// given queue may use memory proportionate to the product of its length and
/// the number of distinct tags within it.
#[derive(Debug, Clone)]
pub struct Queue<T> {
    offset: u64,
    first_with_tag: HashMap<usize, u64>,
    info: VecDeque<Info>,
    values: VecDeque<T>,
}

/// An item from the queue, either one that is currently in it, or one that has
/// been removed, e.g. by `pop()`. For a queue of values of type `T`, different
/// methods will return `Item<T>`, `Item<&T>` and `Item<&mut T>`, as appropriate
/// to the borrowing properties of that method.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Item<T> {
    index: u64,
    tag: usize,
    value: T,
}

impl<T> Item<T> {
    /// The index of the item: this is unique for the entire lifetime of the
    /// queue from which this item originated.
    pub fn index(&self) -> u64 { self.index }
    /// The tag of the item which was originally assigned when the item was
    /// inserted into the queue.
    pub fn tag(&self) -> usize { self.tag }
    /// Extract the value itself. If this is an `Item<&T>` or an `Item<&mut T>`
    /// and you just want a reference to the value without consuming the `Item`,
    /// use `as_ref()` or `as_mut()`, respectively.
    pub fn into_value(self) -> T { self.value }
}

impl<T> AsRef<T> for Item<&T> {
    fn as_ref(&self) -> &T {
        self.value
    }
}

impl<T> AsMut<T> for Item<&mut T> {
    fn as_mut(&mut self) -> &mut T {
        self.value
    }
}

#[derive(Debug, Clone)]
struct Info {
    tag: usize,
    next_with_tag: usize,
    previous_with_tag: HashMap<usize, u64>,
}

impl Info {
    fn has_tag(&self, tag: usize) -> bool {
        self.tag == tag
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
            let index = $index;
            let this = $self;
            // Find the item, if one exists
            let internal_index = this.as_internal_index(index)?;
            let Info{tag, ..} =
                get!(this.info,
                     internal_index
                     $(, $mutability)?)?;
            Some(Item {
                value: & $($mutability)? this.values[internal_index],
                tag: *tag,
                index
            })
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
            let (previous_tag, previous_index) =
                tags.iter()
                .filter_map(|tag| Some((tag, *current.previous_with_tag.get(tag)?)))
                .max_by_key(|(_, i)| i.clone())?;
            Some(Item {
                value: get!(this.values, this.as_internal_index(previous_index)? $(, $mutability)?)?,
                tag: *previous_tag,
                index: previous_index,
            })
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
            let here_index = index.max(this.first_index());
            let here = this.info(here_index);

            let mut minimum: Option<(usize, u64)> = None;
            if let Some(here_info) = here {
                for tag in tags {
                    if *tag == here_info.tag {
                        minimum = Some((*tag, here_index));
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
                    dbg!(next_index);
                    minimum = match (minimum, next_index) {
                        (None, Some(next_index))
                            if this.first_index() <= next_index => {
                                Some((*tag, next_index))
                            },
                        (Some((_, min)), Some(next_index))
                            if this.first_index() <= next_index && next_index < min => {
                                Some((*tag, next_index))
                            },
                        _ => minimum,
                    }
                }
            } else {
                minimum = this
                    .first_with_tag
                    .iter()
                    .copied()
                    .min_by_key(|(_, i)| i.clone());
            }
            // Get the item at the minimum index and return its exterior-facing
            // index and a reference to the item itself.
            let (next_tag, next_index) = minimum?;
            Some(Item {
                value: get!(this.values, this.as_internal_index(next_index)? $(, $mutability)?)?,
                tag: next_tag,
                index: next_index,
            })
        }
    };
}

impl<T> Queue<T> {
    /// Given an external persistent index, get the current index within the
    /// internal queue that corresponds to it. This correspondence is
    /// invalidated by future changes to the queue.
    fn as_internal_index(&self, index: u64) -> Option<usize> {
        index.checked_sub(self.offset)?.try_into().ok()
    }

    /// Given an internal index in the contained queue, get the persistent index
    /// in the public interface which corresponds to it. This correspondence is
    /// invalidated by future changes to the queue.
    fn as_external_index(&self, index: usize) -> Option<u64> {
        self.offset.checked_add(index as u64)
    }

    fn info(&self, index: u64) -> Option<&Info> {
        self.info.get(self.as_internal_index(index)?)
    }

    fn info_mut(&mut self, index: u64) -> Option<&mut Info> {
        self.info.get_mut(self.as_internal_index(index)?)
    }

    /// Make a new queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = Queue::new();
    /// ```
    pub fn new() -> Queue<T> {
        Self::with_capacity(0)
    }

    /// Make a new queue with a given initial allocated capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = Queue::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Queue<T> {
        Queue {
            offset: 0,
            first_with_tag: HashMap::new(),
            info: VecDeque::with_capacity(capacity),
            values: VecDeque::with_capacity(capacity),
        }
    }

    /// The number of items currently in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = (0..4).zip(0..4).collect();
    /// assert_eq!(queue.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.info.len()
    }

    /// The index which will be assigned to the next item to be added to the
    /// queue, whenever it is added.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = Queue::new();
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

    /// The first index which is still stored in the queue (each `pop`
    /// increments this value by 1).
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// queue.pop();
    /// assert_eq!(queue.first_index(), 2);
    /// ```
    pub fn first_index(&self) -> u64 {
        self.offset
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
    /// let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// queue.clear();
    /// assert_eq!(queue.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.first_with_tag.clear();
        self.info.clear();
        self.values.clear();
    }

    /// Shrink the memory used by the queues in this queue as much as possible.
    /// This is less expensive than `shrink_all_to_fit`, but does not reclaim
    /// excess memory used by items within the queue. Note that such
    /// excessively-sized items in the queue can only be produced using
    /// `push_and_pop`, so it is usually sufficient to use this method.
    pub fn shrink_to_fit(&mut self) {
        self.info.shrink_to_fit();
        self.values.shrink_to_fit();
    }

    /// Get a reference to the first item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// assert_eq!(*queue.get(0).unwrap().as_ref(), 0);
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the queue, even though the
    /// queue still contains items:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// assert!(queue.get(0).is_none());
    /// ```
    pub fn get(&self, index: u64) -> Option<Item<&T>> {
        get_impl!(self, index)
    }

    /// Get a mutable reference to the first item *exactly at* `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// let mut n = queue.get_mut(0).unwrap();
    /// *n.as_mut() = 5000;
    /// assert_eq!(*queue.get(0).unwrap().as_ref(), 5000);
    /// ```
    ///
    /// As noted elsewhere, if we `pop` off this value, the index we
    /// supplied no longer will refer to any item in the queue, even though the
    /// queue still contains items:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<usize> = (0..10).zip(0..10).collect();
    /// queue.pop();
    /// assert!(queue.get(0).is_none());
    /// ```
    pub fn get_mut(&mut self, index: u64) -> Option<Item<&mut T>> {
        get_impl!(self, index, mut)
    }

    /// Get a reference to the first item after or including `index` whose tag
    /// is one of those given.
    ///
    /// # Examples
    ///
    /// Suppose we construct a queue that contains the phrase "Hello world!" in
    /// both English and French, interleaved, each word tagged with its
    /// language (0 = English; 1 = French):
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// let mut queue: Queue<String> =
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
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(0, &[0]).unwrap().as_ref(), "Hello");
    /// assert_eq!(queue.after(0, &[1]).unwrap().as_ref(), "Bonjour");
    /// assert_eq!(queue.after(0, &[0, 1]).unwrap().as_ref(), "Hello");
    /// ```
    ///
    /// Starting *inclusively after* index 1:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(1, &[0]).unwrap().as_ref(), "world!");
    /// assert_eq!(queue.after(1, &[1]).unwrap().as_ref(), "Bonjour");
    /// assert_eq!(queue.after(1, &[0, 1]).unwrap().as_ref(), "Bonjour");
    /// ```
    ///
    /// Starting *inclusively after* index 2:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.after(2, &[0]).unwrap().as_ref(), "world!");
    /// assert_eq!(queue.after(2, &[1]).unwrap().as_ref(), "le monde!");
    /// assert_eq!(queue.after(2, &[0, 1]).unwrap().as_ref(), "world!");
    /// ```
    ///
    /// Starting *inclusively after* index 3:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(queue.after(3, &[0]).is_none());
    /// assert_eq!(queue.after(3, &[1]).unwrap().as_ref(), "le monde!");
    /// assert_eq!(queue.after(3, &[0, 1]).unwrap().as_ref(), "le monde!");
    /// ```
    ///
    /// Starting *inclusively after* index 4:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert!(queue.after(4, &[0]).is_none());
    /// assert!(queue.after(4, &[1]).is_none());
    /// assert!(queue.after(4, &[0, 1]).is_none());
    /// ```
    pub fn after(&self, index: u64, tags: &[usize]) -> Option<Item<&T>> {
        after_impl!(self, index, tags)
    }

    /// Get a mutable reference to the first item after or including `index`
    /// whose tag is one of those given.
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
    /// let mut queue: Queue<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let beginning = 0; // same start index for both calls to `after_mut`
    /// *queue.after_mut(beginning, &[0]).unwrap().as_mut() = "Goodbye".to_string();
    /// *queue.after_mut(beginning, &[1]).unwrap().as_mut() = "Au revoir".to_string();
    ///
    /// assert_eq!(queue.get(0).unwrap().as_ref(), "Goodbye");
    /// assert_eq!(queue.get(1).unwrap().as_ref(), "Au revoir");
    /// ```
    pub fn after_mut(&mut self, index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
        after_impl!(self, index, tags, mut)
    }

    /// Get a reference to the latest item before or including `index` whose tag
    /// is one of those given.
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
    /// let mut queue: Queue<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    /// ```
    ///
    /// Starting from index 4 (which is after the end of the queue), the last
    /// word tagged as English is "world!"; the last tagged as French is "le
    /// monde!"; the last tagged as either is "le monde!":
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(4, &[0]).unwrap().as_ref(), "world!");
    /// assert_eq!(queue.before(4, &[1]).unwrap().as_ref(), "le monde!");
    /// assert_eq!(queue.before(4, &[0, 1]).unwrap().as_ref(), "le monde!");
    /// ```
    ///
    /// Starting *inclusively before* index 3 (the end of the queue), we get
    /// the same results as any query after the end of the queue:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(3, &[0]).unwrap().as_ref(), "world!");
    /// assert_eq!(queue.before(3, &[1]).unwrap().as_ref(), "le monde!");
    /// assert_eq!(queue.before(3, &[0, 1]).unwrap().as_ref(), "le monde!");
    /// ```
    ///
    /// Starting *inclusively before* index 2:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(2, &[0]).unwrap().as_ref(), "world!");
    /// assert_eq!(queue.before(2, &[1]).unwrap().as_ref(), "Bonjour");
    /// assert_eq!(queue.before(2, &[0, 1]).unwrap().as_ref(), "world!");
    /// ```
    ///
    /// Starting *inclusively before* index 1:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(1, &[0]).unwrap().as_ref(), "Hello");
    /// assert_eq!(queue.before(1, &[1]).unwrap().as_ref(), "Bonjour");
    /// assert_eq!(queue.before(1, &[0, 1]).unwrap().as_ref(), "Bonjour");
    /// ```
    ///
    /// Starting *inclusively before* index 0:
    ///
    /// ```
    /// # use hopscotch::Queue;
    /// # let mut queue: Queue<String> =
    /// #   vec![(0, "Hello".to_string()),
    /// #        (1, "Bonjour".to_string()),
    /// #        (0, "world!".to_string()),
    /// #        (1, "le monde!".to_string())].into_iter().collect();
    /// assert_eq!(queue.before(0, &[0]).unwrap().as_ref(), "Hello");
    /// assert!(queue.before(0, &[1]).is_none());
    /// assert_eq!(queue.before(0, &[0, 1]).unwrap().as_ref(), "Hello");
    /// ```
    pub fn before(&self, index: u64, tags: &[usize]) -> Option<Item<&T>> {
        before_impl!(self, index, tags)
    }

    /// Get a mutable reference to the latest item before or including `index`
    /// whose tag is one of those given.
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
    /// let mut queue: Queue<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let end = 5; // same end index for both calls to `after_mut`
    /// *queue.before_mut(end, &[0]).unwrap().as_mut() = "my friends!".to_string();
    /// *queue.before_mut(end, &[1]).unwrap().as_mut() = "mes amis!".to_string();
    ///
    /// assert_eq!(queue.get(2).unwrap().as_ref(), "my friends!");
    /// assert_eq!(queue.get(3).unwrap().as_ref(), "mes amis!");
    /// ```
    pub fn before_mut(&mut self, index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
        before_impl!(self, index, tags, mut)
    }

    /// Pop an item off the back of the queue and return it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<String> = Queue::new();
    /// queue.push(42, "Hello!".to_string());
    /// let item = queue.pop().unwrap();
    ///
    /// assert_eq!(item.index(), 0);
    /// assert_eq!(item.tag(), 42);
    /// assert_eq!(item.into_value(), "Hello!");
    /// ```
    pub fn pop(&mut self) -> Option<Item<T>> {
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
        let popped_next_with_tag =
            popped_index.checked_add(popped_info.next_with_tag as u64);
        let next_index = self.next_index();
        if let Some(next_index_with_tag) = popped_next_with_tag {
            match self.first_with_tag.entry(popped_info.tag) {
                Entry::Occupied(mut entry) => {
                    if next_index_with_tag >= next_index {
                        entry.remove_entry();
                    } else {
                        *entry.get_mut() = next_index_with_tag;
                    }
                },
                Entry::Vacant(_) => {
                    panic!("Queue invariant violation: popped tag not in first_with_tag")
                },
            }
        }
        // Bump the offset because we just shifted the queue
        self.offset = self.offset.checked_add(1).expect("Queue index overflow");
        // Return the pieces
        Some(Item {
            value: popped_value,
            tag: popped_info.tag,
            index: popped_index,
        })
    }

    /// Push a new item into the queue, returning its assigned index.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<String> = Queue::new();
    /// queue.push(0, "Hello!".to_string());
    /// ```
    pub fn push(&mut self, tag: usize, value: T) -> u64 {
        // The index we're about to push
        let pushed_index = self.next_index();
        let mut previous_with_tag =
            self.info.back()
            .map(|latest| latest.previous_with_tag.clone())
            .unwrap_or_else(HashMap::new);
        // Set the next_with_tag index of the previous of this tag to point to
        // the index we're about to insert at.
        previous_with_tag.get(&tag)
            .map(|previous_index| {
                self.info_mut(*previous_index).map(|previous_info| {
                    let distance =
                        (pushed_index - previous_index).try_into()
                        .expect("Queue invariant violation: distance greater than usize::max_value()");
                    previous_info.next_with_tag = distance;
                });
            });
        // Actually insert the item into the queue
        previous_with_tag.insert(tag, pushed_index);
        self.info.push_back(Info {
            tag,
            previous_with_tag,
            next_with_tag: usize::max_value(),
        });
        self.values.push_back(value);
        // Make sure first_with_tag tracks this event, if it is the current
        // first of its tag:
        self.first_with_tag.entry(tag).or_insert(pushed_index);
        // Return the new index
        pushed_index
    }

    /// Get an iterator of immutable items matching any of the given tags, whose
    /// indices are inclusively between `earliest` and `latest`, in order from
    /// lowest to highest index. If `None` is provided for `tags`, every item
    /// between the two bounds is enumerated.
    ///
    /// The returned iterator is double-ended, and therefore can be traversed in
    /// reverse order using the `.rev()` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// let english: Vec<&str> =
    ///     queue.iter_between(0, u64::max_value(), Some(&[0]))
    ///     .map(|i| i.into_value().as_ref()).collect();
    /// assert_eq!(english, &["Hello", "world!"]);
    ///
    /// let all_backwards: Vec<&str> =
    ///     queue.iter_between(0, u64::max_value(), None).rev() // <-- notice the reversal
    ///     .map(|i| i.into_value().as_ref()).collect();
    /// assert_eq!(all_backwards, &["le monde!", "world!", "Bonjour", "Hello"]);
    /// ```
    pub fn iter_between<'a, 'b>(
        &'a self,
        earliest: u64,
        latest: u64,
        tags: Option<&'b [usize]>,
    ) -> Iter<'a, 'b, T> {
        let head = Some(self.next_index().saturating_sub(1).min(latest));
        let tail = Some(self.first_index().max(earliest));
        Iter{inner: self, tags, head, tail}
    }

    /// Get an iterator of mutable items matching any of the given tags, whose
    /// indices are inclusively between `earliest` and `latest`, in order from
    /// lowest to highest index. If `None` is provided for `tags`, every item
    /// between the two bounds is enumerated.
    ///
    /// The returned iterator is double-ended, and therefore can be traversed in
    /// reverse order using the `.rev()` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use hopscotch::Queue;
    ///
    /// let mut queue: Queue<String> =
    ///     vec![(0, "Hello".to_string()),
    ///          (1, "Bonjour".to_string()),
    ///          (0, "world!".to_string()),
    ///          (1, "le monde!".to_string())].into_iter().collect();
    ///
    /// for mut item in queue.iter_between_mut(0, u64::max_value(), Some(&[0])) {
    ///    *item.as_mut() = item.as_mut().to_uppercase();
    /// }
    ///
    /// let words: Vec<&str> =
    ///     queue.iter_between(0, u64::max_value(), None)
    ///     .map(|i| i.into_value().as_ref()).collect();
    /// assert_eq!(words, &["HELLO", "Bonjour", "WORLD!", "le monde!"]);
    /// ```
    pub fn iter_between_mut<'a, 'b>(
        &'a mut self,
        earliest: u64,
        latest: u64,
        tags: Option<&'b [usize]>,
    ) -> IterMut<'a, 'b, T> {
        let head = Some(self.next_index().saturating_sub(1).min(latest));
        let tail = Some(self.first_index().max(earliest));
        IterMut{inner: self, tags, head, tail}
    }
}

impl<T> FromIterator<(usize, T)> for Queue<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (usize, T)>,
    {
        let iter = iter.into_iter();
        let mut queue = Queue::with_capacity(iter.size_hint().0);
        for (tag, item) in iter {
            queue.push(tag, item);
        }
        queue
    }
}

impl<T> Extend<(usize, T)> for Queue<T> {
    fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item = (usize, T)> {
        for (tag, item) in iter {
            self.push(tag, item);
        }
    }
}

/// An iterator over immutable references to items in a queue.
pub struct Iter<'a, 'b, T> {
    inner: &'a Queue<T>,
    tags: Option<&'b [usize]>,
    head: Option<u64>,
    tail: Option<u64>,
}

impl<'a, 'b, T> Iterator for Iter<'a, 'b, T> {
    type Item = Item<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags {
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

impl<'a, 'b, T> DoubleEndedIterator for Iter<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags {
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

/// An iterator over mutable references to items in a queue.
pub struct IterMut<'a, 'b, T: 'a> {
    inner: &'a mut Queue<T>,
    tags: Option<&'b [usize]>,
    head: Option<u64>,
    tail: Option<u64>,
}

// A note on unsafe blocks below: the potential unsafety here would result from
// accidentally aliasing two mutable pointers. This is not possible, because the
// index is always incremented by at least one, which means we'll never produce
// the same thing again -- even in the DoubleEndedIterator case.

impl<'a, 'b, T> Iterator for IterMut<'a, 'b, T> {
    type Item = Item<&'a mut T>;

    fn next(&'_ mut self) -> Option<Item<&'a mut T>> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags {
            self.inner.after_mut(self.tail?, tags)
        } else {
            self.inner.get_mut(self.tail?)
        }?;
        self.tail = item.index.checked_add(1);
        if item.index > self.head? {
            return None;
        }
        Some(Item {
            value: unsafe { &mut *(item.value as *mut _) },
            index: item.index,
            tag: item.tag,
        })
    }
}

impl<'a, 'b, T> DoubleEndedIterator for IterMut<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.tail? > self.head? {
            return None;
        }
        let item = if let Some(tags) = self.tags {
            self.inner.before_mut(self.head?, tags)
        } else {
            self.inner.get_mut(self.head?)
        }?;
        self.head = item.index.checked_sub(1);
        if item.index < self.tail? {
            return None;
        }
        Some(Item {
            value: unsafe { &mut *(item.value as *mut _) },
            index: item.index,
            tag: item.tag,
        })
    }
}

/*
impl<T: std::fmt::Display> std::fmt::Display for Queue<T> {
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
                        .info
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
            .info
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
        for (i, value) in self.info.iter().zip(self.values.iter()) {
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
            write!(f, " | {}", value)?
        }
        Ok(())
    }
}
*/
