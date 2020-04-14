# Hopscotch Queues: Skipping and Jumping Around Tagged, Ordered Data

A `hopscotch::Queue<K, V>` is a first-in-first-out queue where each `Item<K, V>`
in the queue has

- a value of type `V`,
- an immutable tag of type `K`, and
- a unique `index` of type `u64` which is assigned in sequential order of
  insertion starting at 0 when the queue is created.

In addition to supporting the ordinary `push`, `pop`, and `get` methods of a
FIFO queue, a hopscotch queue also supports the special, optimized methods
`after`, `after_mut`, `before`, and `before_mut`.

These methods find the next (or previous) `Item` (or `ItemMut`) in the
queue whose tag is equal to any of a given set of tags. For instance, the
signature of `after` is:

```rust
pub fn after<'a, Tags>(&self, index: u64, tags: Tags) -> Option<Item<K, V>>
    where
        Tags: IntoIterator<Item = &'a K>,
        K: 'a,
```

If we use `&[K]` for `Tags`, this signature simplifies to:

```rust
pub fn after(&self, index: u64, tags: &[K]) -> Option<Item<K, V>>
```

These methods are the real benefit of using a hopscotch queue over another
data structure. Their asymptotic time complexity is:

- linear relative to the number of tags queried,
- logarithmic relative to the total number of distinct tags in the queue,
- constant relative to the length of the queue, and
- constant relative to the distance between successive items with the same
  tag.

Hopscotch queues also provide flexible iterators `Iter(Mut)` to efficiently
traverse portions of their contents, sliced by index using `Iter(Mut)::until` and
`Iter(Mut)::after`, and filtered by set of desired tags using
`Iter(Mut)::matching_only`.

# When might I use this?

This queue performs well when:

- the set of total tags in the queue is small
- the number of query operations is greater than the number of
  insertion/deletion operations
- you can afford a little bit of extra memory for bookkeeping

One use-case for such a structure is implementing a bounded pub/sub event buffer
where clients interested in a particular subset of events repeatedly query for
the next event matching their desired subset. This scenario plays to the
strengths of a hopscotch queue, because each query can be performed very
quickly, regardless of the contents or size of the buffer.

The `push` and `pop` operations are slower by a considerable constant factor
than their equivalents for `VecDeque<(K, T)>`, but for this price, you gain the
ability to skip and hop between sets of tags in almost-constant time.

In scenarios with a few hundred tags, `push` and `pop` operations on my machine
(recent-ish MacBook Pro) take on the order of low single-digits of microseconds
(hundreds of thousands of operations per second), and `after`/`before` queries
take on the order of tens of nanoseconds (tens of millions of operations per
second), depending on the number of tags present in the queue. More detailed and
scientific benchmarks are to come, and please feel free to contribute!

If this is similar to your needs, this data structure might be for you!

# When should I *not* use this?

- If your access pattern to the data in the queue does not frequently make
  queries looking for the next/previous/first/last with a given tag, this queue
  will underperform a simpler `VecDeque<(K, T)>`.
- If you *do* need such query methods, but the distribution of tags is such that
  tags are unlikely to be frequently repeated in the queue (number of tags is
  close to the max size of the queue), this queue will underperform a data
  structure built from a pair of a `VecDeque<T>` of values and a mapping from
  tags to sorted vectors of of indices.
- If most tags will be close to others of their same ilk, and you can tolerate
  an occasional long-lasting linear scan of the queue when this is not the case,
  a simple `VecDeque<(K, T)>` may also suffice.
- If you need to *change* the tag of an item which is already in the queue, this
  data structure will not permit that operation. Allowing this possibility would
  degrade the performance of all other operations on the queue by a constant
  factor, but it is possible that future releases will include this as an
  optional flag.
- If you need to remove an item from the "in" end of the queue, add an item to
  the "out" end of the queue, or insert an item in the middle of the queue,
  these operations would be linear-time or worse for a hopscotch queue, and
  while we may eventually add them as methods, they would not be efficient.
