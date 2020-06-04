use hopscotch;
use quickcheck::{quickcheck, Arbitrary, Gen, QuickCheck};
use std::fmt::Debug;
use std::iter;

/// Check that two double-ended iterators are equal under the sequence of
/// front/back choices specified in the `ordering` iterator (where `true` means
/// pick from front and `false` means pick from the rear).
fn compare_double_ended_iters<T, I, J, K>(mut i: I, mut j: J, ordering: K) -> bool
where
    I: Iterator<Item = T> + DoubleEndedIterator,
    J: Iterator<Item = T> + DoubleEndedIterator,
    K: Iterator<Item = bool>,
    T: Eq,
{
    for side in ordering {
        if side {
            match (i.next(), j.next()) {
                (None, None) => break,
                (Some(x), Some(y)) if x == y => {}
                _ => return false,
            }
        } else {
            match (i.next_back(), j.next_back()) {
                (None, None) => break,
                (Some(x), Some(y)) if x == y => {}
                _ => return false,
            }
        }
    }
    true
}

/// Simulate the iter_between(_mut) method for queues using the iterator for
/// `Vec` as a test case.
fn vec_iter_between<'a, T: Clone>(
    tags: Option<Vec<usize>>,
    lo: usize,
    hi: usize,
    vec: &'a [(usize, T)],
) -> impl Iterator<Item = (usize, T)> + DoubleEndedIterator + 'a {
    vec.iter()
        .cloned()
        .enumerate()
        .filter(move |(i, (t, _))| {
            (tags.is_none() || tags.as_ref().unwrap().contains(&t))
                && *i <= lo.max(hi)
                && *i >= lo.min(hi)
        })
        .map(|p| p.1)
}

quickcheck! {
    // Check the iterator implementations against specifications...
    fn iter_correct(
        input: Vec<(usize, usize)>,
        option_tags: Option<Vec<usize>>,
        ordering: Vec<bool>, // true = front, false = back
        lo: usize,
        hi: usize
    ) -> bool {
        let queue: hopscotch::Queue<usize, usize> =
            input.clone().into_iter().collect();
        let vec_iter = vec_iter_between(option_tags.clone(), lo, hi, &input);
        if let Some(tags) = option_tags {
            let queue_iter =
                queue.iter()
                .after(lo.min(hi) as u64)
                .until(lo.max(hi) as u64)
                .matching_only(&tags)
                .map(|i| (*i.tag(), *i.as_ref()));
            compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
        } else {
            let queue_iter =
                queue.iter()
                .after(lo.min(hi) as u64)
                .until(lo.max(hi) as u64)
                .map(|i| (*i.tag(), *i.as_ref()));
            compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
        }
    }

    fn iter_mut_correct(
        input: Vec<(usize, usize)>,
        option_tags: Option<Vec<usize>>,
        ordering: Vec<bool>, // true = front, false = back
        lo: usize,
        hi: usize
    ) -> bool {
        let mut queue: hopscotch::Queue<usize, usize> =
            input.clone().into_iter().collect();
        let vec_iter = vec_iter_between(option_tags.clone(), lo, hi, &input);
        if let Some(tags) = option_tags {
            let queue_iter =
                queue.iter_mut()
                .after(lo.min(hi) as u64)
                .until(lo.max(hi) as u64)
                .matching_only(&tags)
                .map(|i| (*i.tag(), *i.as_ref()));
            compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
        } else {
            let queue_iter =
                queue.iter_mut()
                .after(lo.min(hi) as u64)
                .until(lo.max(hi) as u64)
                .map(|i| (*i.tag(), *i.as_ref()));
            compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
        }
    }

    fn partial_eq_correct(
        left: Vec<(usize, usize)>,
        right: Vec<(usize, usize)>
    ) -> bool {
        let equal_inputs = left == right;
        let left: hopscotch::Queue<_, _> = left.into_iter().collect();
        let right: hopscotch::Queue<_, _> = right.into_iter().collect();
        if equal_inputs {
            left == right
        } else {
            left != right
        }
    }

    fn partial_ord_correct(
        left: Vec<(usize, usize)>,
        right: Vec<(usize, usize)>
    ) -> bool {
        let left: hopscotch::Queue<_, _> = left.into_iter().collect();
        let right: hopscotch::Queue<_, _> = right.into_iter().collect();
        let compare_as_iters = left.iter().partial_cmp(right.iter());
        let compare_directly = left.partial_cmp(&right);
        compare_as_iters == compare_directly
    }

    fn ord_correct(
        left: Vec<(usize, usize)>,
        right: Vec<(usize, usize)>
    ) -> bool {
        let left: hopscotch::Queue<_, _> = left.into_iter().collect();
        let right: hopscotch::Queue<_, _> = right.into_iter().collect();
        let compare_as_iters = left.iter().cmp(right.iter());
        let compare_directly = left.cmp(&right);
        compare_as_iters == compare_directly
    }
}

#[test]
fn default_is_new() {
    let q: hopscotch::Queue<usize, usize> = hopscotch::Queue::default();
    let r: hopscotch::Queue<usize, usize> = hopscotch::Queue::new();
    if q != r {
        panic!("Queue::default is not Queue::new")
    }
}

/// An enumeration of operations that can be performed on a queue
#[derive(Debug, Clone)]
enum Operation<T> {
    Len,
    IsEmpty,
    Contains(T),
    ContainsTag(usize),
    Clear,
    NextIndex,
    Earliest,
    EarliestMutAndSet(T),
    Latest,
    LatestMutAndSet(T),
    ShrinkToFit,
    Get(u64),
    GetMutAndSet(u64, T),
    After(u64, Vec<usize>),
    AfterMutAndSet(u64, Vec<usize>, T),
    Before(u64, Vec<usize>),
    BeforeMutAndSet(u64, Vec<usize>, T),
    Push(usize, T),
    Pop,
}

impl<T: Arbitrary> Arbitrary for Operation<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        use Operation::*;
        match usize::arbitrary(g) % 19 {
            0 => Len,
            1 => Clear,
            2 => NextIndex,
            3 => Earliest,
            4 => EarliestMutAndSet(T::arbitrary(g)),
            5 => Latest,
            6 => LatestMutAndSet(T::arbitrary(g)),
            7 => ShrinkToFit,
            8 => Get(u64::arbitrary(g)),
            9 => GetMutAndSet(u64::arbitrary(g), T::arbitrary(g)),
            10 => After(u64::arbitrary(g), Vec::arbitrary(g)),
            11 => AfterMutAndSet(u64::arbitrary(g), Vec::arbitrary(g), T::arbitrary(g)),
            12 => Before(u64::arbitrary(g), Vec::arbitrary(g)),
            13 => BeforeMutAndSet(u64::arbitrary(g), Vec::arbitrary(g), T::arbitrary(g)),
            14 => Push(usize::arbitrary(g), T::arbitrary(g)),
            15 => Pop,
            16 => Contains(T::arbitrary(g)),
            17 => ContainsTag(usize::arbitrary(g)),
            18 => IsEmpty,
            _ => panic!("Bad discriminant while generating operation!"),
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        use Operation::*;
        match self {
            Len => Box::new(iter::empty()),
            Clear => Box::new(iter::empty()),
            NextIndex => Box::new(iter::empty()),
            Earliest => Box::new(iter::empty()),
            Latest => Box::new(iter::empty()),
            ShrinkToFit => Box::new(iter::empty()),
            IsEmpty => Box::new(iter::empty()),
            Contains(value) => Box::new(value.shrink().map(Contains)),
            ContainsTag(tag) => Box::new(tag.shrink().map(ContainsTag)),
            EarliestMutAndSet(new) => Box::new(new.shrink().map(EarliestMutAndSet)),
            LatestMutAndSet(new) => Box::new(new.shrink().map(LatestMutAndSet)),
            Get(index) => Box::new(index.shrink().map(Get)),
            GetMutAndSet(index, new) => Box::new(
                (index.clone(), new.clone())
                    .shrink()
                    .map(|(i, n)| GetMutAndSet(i, n)),
            ),
            After(index, tags) => Box::new(
                (index.clone(), tags.clone())
                    .shrink()
                    .map(|(i, ts)| After(i, ts)),
            ),
            AfterMutAndSet(index, tags, new) => Box::new(
                (index.clone(), tags.clone(), new.clone())
                    .shrink()
                    .map(|(i, ts, n)| AfterMutAndSet(i, ts, n)),
            ),
            Before(index, tags) => Box::new(
                (index.clone(), tags.clone())
                    .shrink()
                    .map(|(i, ts)| Before(i, ts)),
            ),
            BeforeMutAndSet(index, tags, new) => Box::new(
                (index.clone(), tags.clone(), new.clone())
                    .shrink()
                    .map(|(i, ts, n)| BeforeMutAndSet(i, ts, n)),
            ),
            Push(tag, value) => Box::new(
                (tag.clone(), value.clone())
                    .shrink()
                    .map(|(t, v)| Push(t, v)),
            ),
            Pop => Box::new(iter::empty()),
        }
    }
}

/// Determine if a given sequence of operations have identical results between
/// the simple specification and the actual queue implementation.
fn simulates_simple_queue(operations: Vec<Operation<usize>>) -> bool {
    let mut complex = hopscotch::Queue::new();
    let mut simple = simple::Queue::new();
    for operation in operations {
        if !simulate(operation, &mut simple, &mut complex) {
            return false;
        }
    }
    true
}

#[test]
fn prop_simulates_simple_queue() {
    QuickCheck::new()
        .tests(1_000_000)
        .quickcheck(simulates_simple_queue as fn(Vec<Operation<usize>>) -> bool)
}

fn simulate<T: Eq + Clone + Debug>(
    operation: Operation<T>,
    simple: &mut simple::Queue<T>,
    complex: &mut hopscotch::Queue<usize, T>,
) -> bool {
    use Operation::*;
    match operation {
        Len => return simple.len() == complex.len(),
        IsEmpty => return simple.is_empty() == complex.is_empty(),
        Clear => {
            simple.clear();
            complex.clear();
        }
        NextIndex => return simple.next_index() == complex.next_index(),
        Contains(value) => return simple.contains(&value) == complex.contains(&value),
        ContainsTag(tag) => return simple.contains_tag(&tag) == complex.contains_tag(&tag),
        Earliest => {
            let s = simple.earliest();
            let c = complex.earliest();
            return s == c.map(hopscotch::Item::into);
        }
        Latest => {
            let s = simple.latest();
            let c = complex.latest();
            return s == c.map(hopscotch::Item::into);
        }
        ShrinkToFit => {
            simple.shrink_to_fit();
            complex.shrink_to_fit();
        }
        Get(index) => {
            let s = simple.get(index);
            let c = complex.get(index);
            return s == c.map(hopscotch::Item::into);
        }
        After(index, tags) => {
            let s = simple.after(index, &tags);
            let c = complex.after(index, &tags);
            return s == c.map(hopscotch::Item::into);
        }
        Before(index, tags) => {
            let s = simple.before(index, &tags);
            let c = complex.before(index, &tags);
            return s == c.map(hopscotch::Item::into);
        }
        EarliestMutAndSet(new) => match (simple.earliest_mut(), complex.earliest_mut()) {
            (None, None) => {}
            (Some(mut s), Some(mut c)) => {
                *s.as_mut() = new.clone();
                *c.as_mut() = new;
            }
            _ => return false,
        },
        LatestMutAndSet(new) => match (simple.latest_mut(), complex.latest_mut()) {
            (None, None) => {}
            (Some(mut s), Some(mut c)) => {
                *s.as_mut() = new.clone();
                *c.as_mut() = new;
            }
            _ => return false,
        },
        GetMutAndSet(index, new) => match (simple.get_mut(index), complex.get_mut(index)) {
            (None, None) => {}
            (Some(mut s), Some(mut c)) => {
                *s.as_mut() = new.clone();
                *c.as_mut() = new;
            }
            _ => return false,
        },
        AfterMutAndSet(index, tags, new) => {
            match (
                simple.after_mut(index, &tags),
                complex.after_mut(index, &tags),
            ) {
                (None, None) => {}
                (Some(mut s), Some(mut c)) => {
                    *s.as_mut() = new.clone();
                    *c.as_mut() = new;
                }
                _ => return false,
            }
        }
        BeforeMutAndSet(index, tags, new) => {
            match (
                simple.before_mut(index, &tags),
                complex.before_mut(index, &tags),
            ) {
                (None, None) => {}
                (Some(mut s), Some(mut c)) => {
                    *s.as_mut() = new.clone();
                    *c.as_mut() = new;
                }
                _ => return false,
            }
        }
        Push(tag, value) => return simple.push(tag, value.clone()) == complex.push(tag, value),
        Pop => return simple.pop() == complex.pop().map(hopscotch::Popped::into),
    }
    true
}

/// A simple reference implementation of the same functionality as a hopscotch
/// queue, with worse asymptotics.
#[allow(dead_code)]
mod simple {
    use hopscotch;
    use std::collections::VecDeque;
    use std::convert::TryInto;

    /// A simple queue which should be behaviorally indistinguishable (but
    /// slower) than a hopscotch queue. Used for testing by bi-simulation.
    #[derive(Debug, Clone)]
    pub(super) struct Queue<T> {
        offset: u64,
        inner: VecDeque<(usize, T)>,
    }

    #[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Item<T> {
        index: u64,
        tag: usize,
        value: T,
    }

    impl<T> Item<T> {
        pub fn index(&self) -> u64 {
            self.index
        }
        pub fn tag(&self) -> usize {
            self.tag
        }
        pub fn value(self) -> T {
            self.value
        }
    }

    impl<T> AsRef<T> for Item<&T> {
        fn as_ref(&self) -> &T {
            &self.value
        }
    }

    impl<T> AsMut<T> for Item<&mut T> {
        fn as_mut(&mut self) -> &mut T {
            &mut self.value
        }
    }

    impl<'a, T> From<hopscotch::Item<'a, usize, T>> for Item<&'a T> {
        fn from(item: hopscotch::Item<'a, usize, T>) -> Item<&'a T> {
            Item {
                index: item.index(),
                tag: *item.tag(),
                value: item.value(),
            }
        }
    }

    impl<'a, T> From<hopscotch::ItemMut<'a, usize, T>> for Item<&'a mut T> {
        fn from(item: hopscotch::ItemMut<'a, usize, T>) -> Item<&'a mut T> {
            Item {
                index: item.index(),
                tag: *item.tag(),
                value: item.into_mut(),
            }
        }
    }

    impl<T> From<hopscotch::Popped<usize, T>> for Item<T> {
        fn from(item: hopscotch::Popped<usize, T>) -> Item<T> {
            Item {
                index: item.index,
                tag: item.tag,
                value: item.value,
            }
        }
    }

    impl<T> Queue<T> {
        pub fn new() -> Queue<T> {
            Self::with_capacity(0)
        }

        pub fn with_capacity(capacity: usize) -> Queue<T> {
            Queue {
                offset: 0,
                inner: VecDeque::with_capacity(capacity),
            }
        }

        pub fn len(&self) -> usize {
            self.inner.len()
        }

        pub fn is_empty(&self) -> bool {
            self.inner.is_empty()
        }

        pub fn clear(&mut self) {
            self.inner.clear();
        }

        pub fn contains(&self, x: &T) -> bool
        where
            T: PartialEq,
        {
            self.inner.iter().find(|i| i.1 == *x).is_some()
        }

        pub fn contains_tag(&self, t: &usize) -> bool {
            self.inner.iter().find(|i| i.0 == *t).is_some()
        }

        pub fn next_index(&self) -> u64 {
            self.offset
                .checked_add(self.len() as u64)
                .expect("Queue index overflow")
        }

        pub fn earliest(&self) -> Option<Item<&T>> {
            let (tag, value) = self.inner.front()?;
            Some(Item {
                index: self.offset,
                tag: *tag,
                value,
            })
        }

        pub fn earliest_mut(&mut self) -> Option<Item<&mut T>> {
            let (tag, value) = self.inner.front_mut()?;
            Some(Item {
                index: self.offset,
                tag: *tag,
                value,
            })
        }

        pub fn latest(&self) -> Option<Item<&T>> {
            let index = self.offset.checked_add(self.len().checked_sub(1)? as u64)?;
            let (tag, value) = self.inner.back()?;
            Some(Item {
                index,
                tag: *tag,
                value,
            })
        }

        pub fn latest_mut(&mut self) -> Option<Item<&mut T>> {
            let index = self.offset.checked_add(self.len().checked_sub(1)? as u64)?;
            let (tag, value) = self.inner.back_mut()?;
            Some(Item {
                index,
                tag: *tag,
                value,
            })
        }

        pub fn shrink_to_fit(&mut self) {
            self.inner.shrink_to_fit();
        }

        pub fn get(&self, index: u64) -> Option<Item<&T>> {
            let inner_index = index.checked_sub(self.offset)?.try_into().ok()?;
            let (tag, value) = self.inner.get(inner_index)?;
            Some(Item {
                index,
                tag: *tag,
                value,
            })
        }

        pub fn get_mut(&mut self, index: u64) -> Option<Item<&mut T>> {
            let inner_index = index.checked_sub(self.offset)?.try_into().ok()?;
            let (tag, value) = self.inner.get_mut(inner_index)?;
            Some(Item {
                index,
                tag: *tag,
                value,
            })
        }

        pub fn after(&self, mut index: u64, tags: &[usize]) -> Option<Item<&T>> {
            index = index.max(self.offset);
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag()) {
                    return Some(item);
                }
                index = index.checked_add(1)?;
            }
        }

        pub fn after_mut(&mut self, mut index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
            index = index.max(self.offset);
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag()) {
                    break;
                }
                index = index.checked_add(1)?;
            }
            self.get_mut(index)
        }

        pub fn before(&self, mut index: u64, tags: &[usize]) -> Option<Item<&T>> {
            index = index.min(self.next_index().saturating_sub(1));
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag()) {
                    return Some(item);
                }
                index = index.checked_sub(1)?;
            }
        }

        pub fn before_mut(&mut self, mut index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
            index = index.min(self.next_index().saturating_sub(1));
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag()) {
                    break;
                }
                index = index.checked_sub(1)?;
            }
            self.get_mut(index)
        }

        pub fn push(&mut self, tag: usize, value: T) -> u64 {
            let index = self.offset + (self.inner.len() as u64);
            self.inner.push_back((tag, value));
            index
        }

        pub fn pop(&mut self) -> Option<Item<T>> {
            let (tag, value) = self.inner.pop_front()?;
            let result = Item {
                tag,
                value,
                index: self.offset,
            };
            self.offset += 1;
            Some(result)
        }
    }
}
