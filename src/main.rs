use std::collections::{VecDeque, HashMap};
use std::convert::TryInto;
use std::io;
use std::cmp::Ordering;

mod sparse;
use sparse::Sparse;

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
#[derive(Debug, Clone)]
pub struct TaggedBuffer<T> {
    offset: u64,
    first_with_tag: HashMap<usize, usize>,
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
                                index.saturating_add(current.next_with_tag)
                            } else {
                                index
                            }
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
                                *$self.first_with_tag.get(&tag)
                                    .unwrap_or(&usize::max_value())
                            }
                        })
                    }).min_by_key(|(_, i)| i.clone())?
                } else {
                    // If the index requested lies before the buffer, pick whichever
                    // event in the set of tags happened first in the buffer
                    $tags.iter().copied()
                        .filter_map(|tag| Some((tag, *$self.first_with_tag.get(&tag)?)))
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
    pub fn new() -> TaggedBuffer<T> {
        Self::with_capacity(0)
    }

    /// Make a new buffer with a given initial allocated capacity.
    pub fn with_capacity(capacity: usize) -> TaggedBuffer<T> {
        TaggedBuffer {
            offset: 0,
            first_with_tag: HashMap::with_capacity(capacity),
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
        self.offset.checked_add(self.queue.len() as u64)
            .expect("Buffer index overflow")
    }

    /// The first index which is still stored in the buffer (each `pop`
    /// increments this value by 1).
    pub fn first_index(&self) -> u64 {
        self.offset
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
        let result = self.pop_and_reclaim()?.0;
        Some(result)
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
        self.first_with_tag.retain(|k, dist| {
            if popped.has_tag(*k) {
                *dist = popped.next_with_tag;
                popped_tag = Some(*k);
            }
            // It's safe to .unwrap() below because:
            // - if popped.has_tag(k), then *dist = popped.next_with_tag
            //   and popped.next_with_tag > 0, because this invariant
            //   always holds for next_with_tag
            // - if !popped.has_tag(k), then *dist > 0 because *dist
            //   should always hold the index of the thing with tag k,
            //   and we know that the thing at index 0 is not with tag k
            if *dist != usize::max_value() {
                *dist = dist.checked_sub(1).unwrap();
                true // keep this thing
            } else {
                false // drop this thing
            }
        });
        // Clear the vec but retain its memory
        popped.previous_with_tag.clear();
        // Bump the offset because we just shifted the queue
        self.offset = self.offset.checked_add(1).expect("Buffer index overflow");
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
        // Calculate the backward distance to the previous of this tag.
        let distance_to_previous =
            self.queue.back().and_then(|latest| {
                latest.previous_with_tag.get(tag).copied()
            }).unwrap_or(usize::max_value()).saturating_add(1);
        // Find the previous of this tag, if any, and set its next_with_tag
        // pointer to point to this new item
        self.queue.len().checked_sub(distance_to_previous)
            .and_then(|i| self.queue.get_mut(i))
            .map(|item| item.next_with_tag = distance_to_previous);
        // Get a fresh vector for tracking the distance to all previous events,
        // either by reclaiming memory of the least recent event (if directed to
        // pop) or by allocating a new one.
        let (popped_item, mut previous_with_tag) =
            if also_pop {
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
            let mut last_inserted = None;
            let skip_to = move |last: Option<usize>, t: usize| {
                match last {
                    None => t,
                    Some(i) => t - i - 1 // we know t > i (strictly) here
                }
            };
            let mut tag_inserted = false;
            let previous_distances = latest.previous_with_tag.iter();
            for (t, dist) in previous_distances {
                match t.cmp(&tag) {
                    Ordering::Less => {
                        if *dist < self.queue.len() {
                            previous_with_tag.skip(skip_to(last_inserted, t));
                            previous_with_tag.push(dist.saturating_add(1));
                            last_inserted = Some(t);
                        }
                    },
                    Ordering::Equal => {
                        previous_with_tag.skip(skip_to(last_inserted, tag));
                        previous_with_tag.push(0);
                        tag_inserted = true;
                        last_inserted = Some(tag);
                    },
                    Ordering::Greater => {
                        if !tag_inserted {
                            previous_with_tag.skip(skip_to(last_inserted, tag));
                            previous_with_tag.push(0);
                            tag_inserted = true;
                            last_inserted = Some(tag);
                        }
                        if *dist < self.queue.len() {
                            previous_with_tag.skip(skip_to(last_inserted, t));
                            previous_with_tag.push(dist.saturating_add(1));
                            last_inserted = Some(t);
                        }
                    }
                }
            }
            if previous_with_tag.len() <= tag {
                previous_with_tag.skip(skip_to(last_inserted, tag));
                previous_with_tag.push(0);
            }
        } else {
            previous_with_tag.skip(tag);
            previous_with_tag.push(0);
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
        if !self.first_with_tag.contains_key(&tag) {
            self.first_with_tag.insert(tag, self.queue.len() - 1);
        }
        // Calculate the index of the just-inserted thing
        (self.offset.checked_add(self.queue.len() as u64)
         .expect("Buffer index overflow") - 1,
         popped_item)
    }
}

impl<T: std::fmt::Display> std::fmt::Display for TaggedBuffer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let max_spaces =
            format!("{}", self.first_with_tag.values()
                    .filter(|x| **x != usize::max_value())
                    .max().unwrap_or(&0).max(
                        &self.queue.iter().map(|i| {
                            (if i.next_with_tag == usize::max_value() { 0 } else { i.next_with_tag })
                                .max(*i.previous_with_tag.values()
                                     .filter(|x| **x != usize::max_value())
                                     .max().unwrap_or(&0))
                        }).max().unwrap_or(0)
                    )).len();
        let max_width =
            self.queue.iter().map(|i| i.previous_with_tag.len())
            .max().unwrap_or(0);
        let spaces = |f: &mut std::fmt::Formatter, s: String| {
            write!(f, "{}", s)?;
            for _ in 0 .. max_spaces.saturating_sub(s.len()) {
                write!(f, "   ")?
            };
            Ok(())
        };
        let dist = |n: usize| {
            if n != usize::max_value() {
                format!("{}", n)
            } else {
                "∞".to_string()
            }
        };
        for _ in 0 .. max_width {
            write!(f, " ")?;
            spaces(f, " ↱ ".to_string())?;
        }
        write!(f, " →")?;
        for t in 0 .. max_width {
            if let Some(d) = self.first_with_tag.get(&t) {
                write!(f, " ")?;
                spaces(f, format!(" ↓{}", dist(*d)))?;
            } else {
                write!(f, " ")?;
                spaces(f, format!("  "))?;
            }
        }
        for i in &self.queue {
            write!(f, "\n")?;
            for t in 0 .. max_width {
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
            for t in 0 .. max_width {
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
