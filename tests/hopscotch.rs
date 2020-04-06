use quickcheck::{quickcheck, QuickCheck, Arbitrary, Gen};
use std::fmt::Debug;
use std::iter;
use hopscotch;

/// Check that two double-ended iterators are equal under the sequence of
/// front/back choices specified in the `ordering` iterator (where `true` means
/// pick from front and `false` means pick from the rear).
fn compare_double_ended_iters<T, I, J, K>(mut i: I, mut j: J, ordering: K) -> bool
where I: Iterator<Item = T> + DoubleEndedIterator,
      J: Iterator<Item = T> + DoubleEndedIterator,
      K: Iterator<Item = bool>,
      T: Eq {
    for side in ordering {
        if side {
            match (i.next(), j.next()) {
                (None, None) => break,
                (Some(x), Some(y)) if x == y => { },
                _ => return false,
            }
        } else {
            match (i.next_back(), j.next_back()) {
                (None, None) => break,
                (Some(x), Some(y)) if x == y => { },
                _ => return false,
            }
        }
    }
    true
}

/// Simulate the iter_between(_mut) method for queues using the iterator for
/// `Vec` as a test case.
fn vec_iter_between<'a, T: Clone>(
    tags: &'a Option<&'a [usize]>, lo: usize, hi: usize, vec: &'a [(usize, T)]
) -> impl Iterator<Item = (usize, T)> + DoubleEndedIterator + 'a {
    vec.iter().cloned().enumerate()
        .filter(move |(i, (t, _))| {
            (tags.is_none() || tags.unwrap().contains(&t))
                && *i <= lo.max(hi) && *i >= lo.min(hi)
        }).map(|p| p.1)
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
        let tags = if let Some(tags) = option_tags.as_ref() {
            Some(tags.as_slice())
        } else {
            None
        };
        let queue: hopscotch::Queue<usize> =
            input.clone().into_iter().collect();
        let queue_iter =
            queue.iter_between(lo.min(hi) as u64, lo.max(hi) as u64, tags)
            .map(|i| (i.tag(), *i.as_ref()));
        let vec_iter = vec_iter_between(&tags, lo, hi, &input);
        compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
    }

    fn iter_mut_correct(
        input: Vec<(usize, usize)>,
        option_tags: Option<Vec<usize>>,
        ordering: Vec<bool>, // true = front, false = back
        lo: usize,
        hi: usize
    ) -> bool {
        let tags = if let Some(tags) = option_tags.as_ref() {
            Some(tags.as_slice())
        } else {
            None
        };
        let mut queue: hopscotch::Queue<usize> =
            input.clone().into_iter().collect();
        let queue_iter =
            queue.iter_between_mut(lo.min(hi) as u64, lo.max(hi) as u64, tags)
            .map(|mut i| (i.tag(), *i.as_mut()));
        let vec_iter = vec_iter_between(&tags, lo, hi, &input);
        compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
    }
}

/// An enumeration of operations that can be performed on a queue
#[derive(Debug, Clone)]
enum Operation<T> {
    Len,
    Clear,
    NextIndex,
    FirstIndex,
    ShrinkToFit,
    ShrinkAllToFit,
    Get(u64),
    GetMutAndSet(u64, T),
    After(u64, Vec<usize>),
    AfterMutAndSet(u64, Vec<usize>, T),
    Before(u64, Vec<usize>),
    BeforeMutAndSet(u64, Vec<usize>, T),
    Push(usize, T),
    Pop,
    PopAndPush(usize, T, bool),
}

impl<T: Arbitrary> Arbitrary for Operation<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        use Operation::*;
        match usize::arbitrary(g) % 15 {
            0 => Len,
            1 => Clear,
            2 => NextIndex,
            3 => FirstIndex,
            4 => ShrinkToFit,
            5 => ShrinkAllToFit,
            6 => Get(u64::arbitrary(g)),
            7 => GetMutAndSet(u64::arbitrary(g), T::arbitrary(g)),
            8 => After(u64::arbitrary(g), Vec::arbitrary(g)),
            9 => AfterMutAndSet(u64::arbitrary(g), Vec::arbitrary(g), T::arbitrary(g)),
            10 => Before(u64::arbitrary(g), Vec::arbitrary(g)),
            11 => BeforeMutAndSet(u64::arbitrary(g), Vec::arbitrary(g), T::arbitrary(g)),
            12 => Push(usize::arbitrary(g), T::arbitrary(g)),
            13 => Pop,
            14 => PopAndPush(usize::arbitrary(g), T::arbitrary(g), bool::arbitrary(g)),
            _ => panic!("Bad discriminant while generating operation!"),
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        use Operation::*;
        match self {
            Len => Box::new(iter::empty()),
            Clear => Box::new(iter::empty()),
            NextIndex => Box::new(iter::empty()),
            FirstIndex => Box::new(iter::empty()),
            ShrinkToFit => Box::new(iter::empty()),
            ShrinkAllToFit => Box::new(iter::empty()),
            Get(index) => Box::new(index.shrink().map(Get)),
            GetMutAndSet(index, new) =>
                Box::new((index.clone(), new.clone()).shrink()
                        .map(|(i, n)| GetMutAndSet(i, n))),
            After(index, tags) =>
                Box::new((index.clone(), tags.clone()).shrink()
                        .map(|(i, ts)| After(i, ts))),
            AfterMutAndSet(index, tags, new) =>
                Box::new((index.clone(), tags.clone(), new.clone()).shrink()
                        .map(|(i, ts, n)| AfterMutAndSet(i, ts, n))),
            Before(index, tags) =>
                Box::new((index.clone(), tags.clone()).shrink()
                        .map(|(i, ts)| Before(i, ts))),
            BeforeMutAndSet(index, tags, new) =>
                Box::new((index.clone(), tags.clone(), new.clone()).shrink()
                        .map(|(i, ts, n)| BeforeMutAndSet(i, ts, n))),
            Push(tag, value) =>
                Box::new((tag.clone(), value.clone()).shrink()
                        .map(|(t, v)| Push(t, v))),
            Pop => Box::new(iter::empty()),
            PopAndPush(tag, value, shrink) =>
                Box::new((tag.clone(), value.clone(), shrink.clone()).shrink()
                        .map(|(t, v, s)| PopAndPush(t, v, s))),
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
        .tests(1_000)
        .quickcheck(simulates_simple_queue as fn(Vec<Operation<usize>>) -> bool)
}

fn simulate<T: Eq + Clone + Debug>(
    operation: Operation<T>,
    simple: &mut simple::Queue<T>,
    complex: &mut hopscotch::Queue<T>,
) -> bool {
    use Operation::*;
    match operation {
        Len => return simple.len() == complex.len(),
        Clear => {
            simple.clear();
            complex.clear();
        },
        NextIndex => return simple.next_index() == complex.next_index(),
        FirstIndex => return simple.first_index() == complex.first_index(),
        ShrinkToFit => {
            simple.shrink_to_fit();
            complex.shrink_to_fit();
        },
        ShrinkAllToFit => {
            simple.shrink_all_to_fit();
            complex.shrink_all_to_fit();
        },
        Get(index) => {
            let s = simple.get(index);
            let c = complex.get(index);
            return s == c.map(hopscotch::Item::into);
        },
        After(index, tags) => {
            let s = simple.after(index, &tags);
            let c = complex.after(index, &tags);
            return s == c.map(hopscotch::Item::into);
        },
        Before(index, tags) => {
            let s = simple.before(index, &tags);
            let c = complex.before(index, &tags);
            return s == c.map(hopscotch::Item::into);
        },
        GetMutAndSet(index, new) => {
            match (simple.get_mut(index), complex.get_mut(index)) {
                (None, None) => { },
                (Some(mut s), Some(mut c)) => {
                    *s.as_mut() = new.clone();
                    *c.as_mut() = new;
                },
                _ => return false,
            }
        },
        AfterMutAndSet(index, tags, new) => {
            match (simple.after_mut(index, &tags), complex.after_mut(index, &tags)) {
                (None, None) => { },
                (Some(mut s), Some(mut c)) => {
                    *s.as_mut() = new.clone();
                    *c.as_mut() = new;
                },
                _ => return false,
            }
        },
        BeforeMutAndSet(index, tags, new) => {
            match (simple.before_mut(index, &tags), complex.before_mut(index, &tags)) {
                (None, None) => { },
                (Some(mut s), Some(mut c)) => {
                    *s.as_mut() = new.clone();
                    *c.as_mut() = new;
                },
                _ => return false,
            }
        },
        Push(tag, value) =>
            return simple.push(tag, value.clone()) == complex.push(tag, value),
        Pop => return simple.pop() == complex.pop().map(hopscotch::Item::into),
        PopAndPush(tag, value, shrink) => {
            let (i, s) = simple.push_and_pop(tag, value.clone(), shrink);
            let (j, c) = complex.push_and_pop(tag, value, shrink);
            return (i, s) == (j, c.map(hopscotch::Item::into));
        },
    }
    true
}

/// A simple reference implementation of the same functionality as a hopscotch
/// queue, with worse asymptotics.
mod simple {
    use std::convert::TryInto;
    use std::collections::VecDeque;
    use hopscotch;

    /// A simple queue which should be behaviorally indistinguishable (but
    /// slower) than a hopscotch queue. Used for testing by bi-simulation.
    #[derive(Debug, Clone)]
    pub(super) struct Queue<T> {
        offset: u64,
        inner: VecDeque<(usize, T)>
    }

    #[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Item<T> {
        index: u64,
        tag: usize,
        value: T,
    }

    impl<T> Item<T> {
        pub fn index(&self) -> u64 { self.index }
        pub fn tag(&self) -> usize { self.tag }
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

    impl<T> From<hopscotch::Item<T>> for Item<T> {
        fn from(item: hopscotch::Item<T>) -> Item<T> {
            Item {
                index: item.index(),
                tag: item.tag(),
                value: item.into_value()
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

        pub fn clear(&mut self) {
            self.inner.clear();
        }

        pub fn next_index(&self) -> u64 {
            self.offset
                .checked_add(self.len() as u64)
                .expect("Queue index overflow")
        }

        pub fn first_index(&self) -> u64 {
            self.offset
        }

        pub fn shrink_to_fit(&mut self) {
            self.inner.shrink_to_fit();
        }

        pub fn shrink_all_to_fit(&mut self) {
            self.shrink_to_fit();
        }

        pub fn get(&self, index: u64) -> Option<Item<&T>> {
            let inner_index = index.checked_sub(self.offset)?.try_into().ok()?;
            let (tag, value) = self.inner.get(inner_index)?;
            Some(Item{index, tag: *tag, value})
        }

        pub fn get_mut(&mut self, index: u64) -> Option<Item<&mut T>> {
            let inner_index = index.checked_sub(self.offset)?.try_into().ok()?;
            let (tag, value) = self.inner.get_mut(inner_index)?;
            Some(Item{index, tag: *tag, value})
        }

        pub fn after(&self, mut index: u64, tags: &[usize]) -> Option<Item<&T>> {
            index = index.max(self.first_index());
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag()) {
                    return Some(item)
                }
                index = index.checked_add(1)?;
            }
        }

        pub fn after_mut(&mut self, mut index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
            index = index.max(self.first_index());
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
                    return Some(item)
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
            let result = Item{tag, value, index: self.offset};
            self.offset += 1;
            Some(result)
        }

        pub fn push_and_pop(&mut self, tag: usize, value: T, _shrink: bool) -> (u64, Option<Item<T>>) {
            let popped = self.pop();
            let index = self.push(tag, value);
            (index, popped)
        }
    }
}
