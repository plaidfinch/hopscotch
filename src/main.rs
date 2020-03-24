use std::collections::VecDeque;
use std::convert::TryInto;
use std::io;

mod distance;
use distance::{Distance, INFINITY};

fn main() {
    let mut count = 0;
    let mut buffer: TaggedBuffer<usize> =
        TaggedBuffer::with_capacity(5);
    loop {
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {
                match input.trim().split(' ').collect::<Vec<_>>().as_slice() {
                    ["push", k] => {
                        let tag = k.trim().parse().unwrap();
                        let i = buffer.push(tag, count);
                        println!("{}", buffer);
                        println!("Result: {:?}", i);
                        count += 1;
                    },
                    ["push_and_pop", k] => {
                        let tag = k.trim().parse().unwrap();
                        let i = buffer.push_and_pop(tag, count);
                        println!("{}", buffer);
                        println!("Result: {:?}", i);
                        count += 1;
                    },
                    ["pop"] => {
                        let r = buffer.pop();
                        println!("{}", buffer);
                        println!("Result: {:?}", r);
                    },
                    ["get", i, ks @ ..] => {
                        let tags: Vec<usize> =
                            ks.iter().map(|k| k.trim().parse().expect("event tag number")).collect();
                        let r = buffer.get_from(i.trim().parse().expect("event index number"), &tags);
                        println!("Result: {:?}", &r);
                    },
                    ["get_after", i, ks @ ..] => {
                        let tags: Vec<usize> =
                            ks.iter().map(|k| k.trim().parse().unwrap()).collect();
                        let r = buffer.get_after(i.trim().parse().unwrap(), &tags);
                        println!("Result: {:?}", &r);
                    },
                    l => {
                        println!("Unrecognized command: {:?}", l)
                    }
                }
            }
            Err(err) => eprintln!("error: {}", err)
        }
    }
}

/// A `TaggedBuffer` is a first-in-first-out (FIFO) queue where each item in the
/// queue is additionally associated with a *tag* of type `usize` and a uniquely
/// assigned sequential *index* of type `u64`. Unlike in a queue like
/// `VecDeque`, queue operations *do not* change the `index` of items; the index
/// is fixed from the time of the item's insertion to its removal, and each new
/// inserted item is given an index one greater than that inserted before it.
///
/// In addition to supporting the ordinary `push`, `pop`, and `get` methods of a
/// FIFO queue, a `TaggedBuffer` supports the methods `get_from` and `get_after`
/// (and their respective `mut` variants), which query the queue to determine
/// the next item in the queue whose `tag` is any of a given set of tags. Given
/// a fixed set of tags in use in the queue, these methods run in time
/// proportionate to the number of tags queried, and constant relative to the
/// size of the queue and the distance between successive items of the same tag.
///
/// **Important:** `TaggedBuffer`s use a "dense" representation to support very
/// fast lookup, but this means they are only memory-efficient when the set of
/// tags is itself small and dense. That is, the memory used by an item in a
/// `TaggedBuffer` is proportionate to the *value* of its tag: so, for instance,
/// an item with tag `1_000_000` will consume approximately 1 MB of space,
/// whereas an item with tag `1` will consume a handful of bytes.
#[derive(Debug, Clone)]
pub struct TaggedBuffer<T> {
    offset: u64,
    first_with_tag: Vec<Distance>,
    queue: VecDeque<InternalItem<T>>,
}

/// An item from the buffer, either one that is currently in it, or one that has
/// been removed, e.g. by `pop()`. For a buffer of values of type `T`, different
/// methods will return `Item<T>`, `Item<&T>` and `Item<&mut T>`, as appropriate
/// to the borrowing properties of that method.
#[derive(Debug, Clone)]
pub struct Item<T> {
    pub index: u64,
    pub tag: usize,
    pub value: T,
}

#[derive(Debug, Clone)]
struct InternalItem<T> {
    value: T,
    next_with_tag: Distance,
    previous_with_tag: Vec<Distance>,
}

impl<T> InternalItem<T> {
    fn has_tag(&self, tag: usize) -> bool {
        if let Some(Distance(0)) = self.previous_with_tag.get(tag) {
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
            for (t, Distance(d)) in previous_with_tag.iter().copied().enumerate() {
                if d == 0 {
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
macro_rules! get_from_or_after_impl {
    ($self:expr, $index:expr, $tags:expr, $exclusively_after:expr $(, $mutability:tt)?) => {
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
                            if $exclusively_after {
                                // If we requested the exclusively-after event,
                                // we should look to the next event of this tag
                                // rather than this event itself
                                index + current.next_with_tag
                            } else {
                                index
                            }
                        } else {
                            // Get the distance backwards to the previous of
                            // this tag.
                            let distance =
                                current.previous_with_tag.get(tag)
                                .unwrap_or(&INFINITY);
                            // Get the index of the previous of this tag
                            if let Some(previous_index) = index - *distance {
                                // If index is >= 0, then find index of the next
                                // of tag. This will be ahead of the current
                                // index, because next_k(previous_k(current_k'))
                                // where k != k' can't lie before current_k' or
                                // else previous_k should have been next_k, a
                                // contradiction.
                                $self.queue.get(previous_index)
                                    .map_or(0 + INFINITY,
                                            |item| index + item.next_with_tag - 1)
                            } else {
                                // If previous_index is < 0, then find index of
                                // the first of this tag. This case happens when
                                // there were no preceding events of the
                                // particular tag, but there might be ones in
                                // the future of it.
                                0 + *$self.first_with_tag.get(tag)
                                    .unwrap_or(&INFINITY)
                            }
                        })
                    }).min_by_key(|(_, i)| i.clone())?
                } else {
                    // If the index requested lies before the buffer, pick whichever
                    // event in the set of tags happened first in the buffer
                    $tags.iter().copied()
                        .filter_map(|tag| Some((tag, 0usize + *$self.first_with_tag.get(tag)?)))
                        .min_by_key(|(_, i)| i.clone())?
                };
            // Get the item at the minimum index and return its exterior-facing
            // index and a reference to the item itself.
            let item = get!($self.queue, next_index $(, $mutability)?)?;
            Some(Item {
                value: & $($mutability)? item.value,
                tag: next_index_tag,
                index: next_index as u64 + $self.offset
            })
        }
    };
}

impl<T> TaggedBuffer<T> {
    /// Make a new buffer.
    pub fn new() -> TaggedBuffer<T> {
        Self::with_capacity(0)
    }

    /// Make a new buffer with a given initial allocated capacity.
    pub fn with_capacity(capacity: usize) -> TaggedBuffer<T> {
        TaggedBuffer {
            offset: 0,
            first_with_tag: Vec::new(),
            queue: VecDeque::with_capacity(capacity)
        }
    }

    /// The number of items currently in the buffer.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    /// The index which will be assigned to the next item to be added to the
    /// buffer, whenever it is added.
    pub fn next_index(&self) -> u64 {
        self.offset + self.queue.len() as u64
    }

    /// Clear the contents of the buffer without de-allocating the queue's
    /// memory (though memory will still be freed for the individual elements of
    /// the queue).
    pub fn clear(&mut self) {
        self.first_with_tag.clear();
        self.queue.clear();
    }

    /// Get a reference to the first item *exactly at* `index`.
    pub fn get(&self, index: u64) -> Option<Item<&T>> {
        get_impl!(self, index)
    }

    /// Get a mutable reference to the first item *exactly at* `index`.
    pub fn get_mut(&mut self, index: u64) -> Option<Item<&mut T>> {
        get_impl!(self, index, mut)
    }

    /// Get a reference to the first item after *or including* `index` whose
    /// tag is one of those given.
    pub fn get_from(&self, index: u64, tags: &[usize]) -> Option<Item<&T>> {
        get_from_or_after_impl!(self, index, tags, false)
    }

    /// Get a mutable reference to the first item after *or including* `index`
    /// whose tag is one of those given.
    pub fn get_from_mut(&mut self, index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
        get_from_or_after_impl!(self, index, tags, false, mut)
    }

    /// Get a reference to the first item *exclusively after* `index` whose
    /// tag is one of those given.
    pub fn get_after(&self, index: u64, tags: &[usize]) -> Option<Item<&T>> {
        get_from_or_after_impl!(self, index, tags, true)
    }

    /// Get a mutable reference to the first item *exclusively after* `index`
    /// whose tag is one of those given.
    pub fn get_after_mut(&mut self, index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
        get_from_or_after_impl!(self, index, tags, true, mut)
    }

    /// Pop an item off the back of the buffer and return it.
    pub fn pop(&mut self) -> Option<Item<T>> {
        let old_length = self.first_with_tag.len();
        let result = self.pop_and_reclaim()?.0;
        // Trim the length of first_with_tag, since it may not need to be as
        // long anymore if the popped item was the maximum width one in the
        // queue. We can always trim the first_with_tag like this, because its
        // non-INFINITY prefix is always exactly the length of that of the front
        // of the queue, since they need to point to the same tags.
        self.first_with_tag.truncate(if let Some(i) = self.queue.front() {
            i.previous_with_tag.len()
        } else {
            0
        });
        if old_length != self.first_with_tag.len() {
            self.first_with_tag.shrink_to_fit();
        }
        Some(result)
    }

    /// Pop an item off the buffer and reclaim the memory it used, so we can
    /// avoid needless allocations. This is an internal-only function.
    fn pop_and_reclaim(&mut self) -> Option<(Item<T>, Vec<Distance>)> {
        // The index of the thing that's about to get popped is equal to
        // the current offset, because the offset is incremented exactly
        // every time something is popped:
        let popped_index = self.offset;
        // Pop off the least recent item:
        let mut popped = self.queue.pop_front()?;
        // Decrement the forward distance for first_with_tag of every
        // event tag *except* the current
        let mut popped_tag = None;
        for (k, dist) in self.first_with_tag.iter_mut().enumerate() {
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
            *dist = (*dist - Distance(1)).unwrap();
        }
        // Clear the vec but retain its memory
        popped.previous_with_tag.clear();
        // Bump the offset because we just shifted the queue
        self.offset += 1;
        // Return the pieces
        Some((Item {
            value: popped.value,
            tag: popped_tag.expect("No 0 element in popped item"),
            index: popped_index
        }, popped.previous_with_tag))
    }

    /// Push a new item into the buffer, returning its assigned index.
    pub fn push(&mut self, tag: usize, value: T) -> u64 {
        self.push_and_maybe_pop(tag, value, false).0
    }

    /// Push a new item into the buffer, evicting the least recent item from the
    /// buffer at the same time, and returning that old item, if one existed.
    /// This is equivalent to calling `pop` and then `push`, but is more
    /// efficient because it saves allocations.
    pub fn push_and_pop(&mut self, tag: usize, value: T) -> (u64, Option<Item<T>>) {
        self.push_and_maybe_pop(tag, value, true)
    }

    /// Push a new item into the buffer, potentially evicting an old item if the
    /// buffer is full. Returns the index of the newly pushed item paired with
    /// the old item and its own index, if an old item was evicted.
    fn push_and_maybe_pop(
        &mut self, tag: usize, value: T, also_pop: bool
    ) -> (u64, Option<Item<T>>) {
        // Grow the first_with_tag vector if the tag is too big
        if tag >= self.width() {
            self.first_with_tag.reserve(self.width().saturating_sub(tag));
            for _ in self.width() ..= tag {
                self.first_with_tag.push(INFINITY)
            }
        }
        // Calculate the backward distance to the previous of this tag.
        let distance_to_previous =
            self.queue.back().and_then(|latest| {
                latest.previous_with_tag.get(tag).cloned()
            }).unwrap_or(INFINITY) + Distance(1);
        // Find the previous of this tag, if any, and set its next_with_tag
        // pointer to point to this new item
        if let Some(item) =
            (self.queue.len() - distance_to_previous)
            .and_then(|i| self.queue.get_mut(i))
        {
            item.next_with_tag = distance_to_previous;
        }
        // Get a fresh vector for tracking the distance to all previous events,
        // either by reclaiming memory of the least recent event (if directed to
        // pop) or by allocating a new one.
        let (popped_item, mut previous_with_tag) =
            if also_pop {
                if let Some((item, vec)) = self.pop_and_reclaim() {
                    (Some(item), vec)
                } else {
                    (None, Vec::new())
                }
            } else {
                (None, Vec::new())
            };
        // Populate the vector with the relative backward distances to the
        // previous events of each tag, omitting any trailing string of
        // INFINITY's, to save space.
        if let Some(latest) = self.queue.back() {
            let mut deferred = 0; // track how many INFINITY we have yet to add
            for t in 0 .. self.width() {
                // The distance to the previous thing of this tag, or INFINITY
                // if there is none in the buffer anymore
                let dist = if t == tag {
                    Distance(0)
                } else {
                    if let Some(latest_dist) = latest.previous_with_tag.get(t) {
                        let dist = *latest_dist + Distance(1);
                        if dist > Distance(self.queue.len()) {
                            INFINITY
                        } else {
                            dist
                        }
                    } else {
                        INFINITY
                    }
                };
                // We omit any string of trailing INFINITY's at the end of a
                // vector, to save memory
                if dist == INFINITY {
                    deferred += 1; // defer putting this in until we need to
                } else {
                    // add all deferred INFINITY's since we need to put a
                    // non-INFINITY value into the vector
                    for _ in 0 .. deferred { previous_with_tag.push(INFINITY) }
                    deferred = 0;
                    previous_with_tag.push(dist);
                }
            }
        } else {
            // Save memory by only pushing the INFINITY's *before* the zero here
            for _ in 0 .. tag { previous_with_tag.push(INFINITY) }
            previous_with_tag.push(Distance(0));
        }
        // Free memory from the given vec that isn't necessary anymore
        previous_with_tag.shrink_to_fit();
        // Reclaim memory in first_with_tag that is no longer needed. There's a
        // subtle invariant here which makes this okay: the initial
        // (non-infinity) bit of the most recent previous_with_tag vec is always
        // the same size as the initial such bit of the first_with_tag vec. Why?
        // If it were not the case, then either first_with_tag would refer to
        // some item not pointed to by previous_with_tag, or vice-versa.
        if previous_with_tag.len() < self.first_with_tag.len() {
            self.first_with_tag.truncate(previous_with_tag.len());
            self.first_with_tag.shrink_to_fit();
        }
        // Actually insert the item into the queue
        self.queue.push_back(InternalItem {
            value,
            next_with_tag: INFINITY,
            previous_with_tag,
        });
        // Make sure first_with_tag tracks this event, if it is the current
        // first of its tag:
        if let Some(first) = self.first_with_tag.get_mut(tag) {
            if *first == INFINITY {
                *first = Distance(self.queue.len() - 1)
            }
        }
        // Calculate the index of the just-inserted thing
        (self.offset + (self.queue.len() as u64) - 1, popped_item)
    }

    /// The current width of the buffer, i.e. the maximum tag number that has
    /// ever been encountered.
    fn width(&self) -> usize {
        self.first_with_tag.len()
    }
}

impl<T: std::fmt::Display> std::fmt::Display for TaggedBuffer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let max_spaces =
            format!("{}", self.first_with_tag.iter().max().unwrap_or(&Distance(0)).max(
                &self.queue.iter().map(|i| {
                    i.next_with_tag.max(*i.previous_with_tag.iter().max().unwrap_or(&Distance(0)))
                }).max().unwrap_or(Distance(0))
            )).len();
        let max_width =
            self.queue.iter().map(|i| i.previous_with_tag.len())
            .max().unwrap_or(0);
        let spaces = |f: &mut std::fmt::Formatter, s: String| {
            write!(f, "{}", s)?;
            for _ in 0 .. max_spaces.saturating_sub(s.len()) {
                write!(f, " ")?
            };
            Ok(())
        };
        for _ in 0 .. max_width {
            write!(f, " ")?;
            spaces(f, " ↱ ".to_string())?;
        }
        write!(f, " →")?;
        for d in &self.first_with_tag {
            write!(f, " ")?;
            spaces(f, format!(" ↓{}", d))?;
        }
        for i in &self.queue {
            write!(f, "\n")?;
            for t in 0 .. max_width {
                if let Some(d) = i.previous_with_tag.get(t) {
                    if d > &Distance(0) {
                        write!(f, " ")?;
                        spaces(f, format!(" ↑{}", d))?;
                    } else {
                        spaces(f, format!(" ({})", t))?;
                    }
                } else {
                    write!(f, " ")?;
                    spaces(f, "".to_string())?;
                }
            }
            write!(f, " |")?;
            for t in 0 .. self.width() {
                if let Some(d) = i.previous_with_tag.get(t) {
                    if d == &Distance(0) {
                        write!(f, " ")?;
                        spaces(f, format!(" ↓{}", i.next_with_tag))?;
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
