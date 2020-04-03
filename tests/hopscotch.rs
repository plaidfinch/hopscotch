use quickcheck::quickcheck;

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
            .map(|i| (i.tag, *i.value));
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
            .map(|i| (i.tag, *i.value));
        let vec_iter = vec_iter_between(&tags, lo, hi, &input);
        compare_double_ended_iters(queue_iter, vec_iter, ordering.into_iter())
    }
}

/// An enumeration of operations that can be performed on a queue
enum Operation<T> {
    Len,
    Clear,
    NextIndex,
    FirstIndex,
    ShrinkToFit,
    ShrinkAllToFit,
    Get(usize),
    GetMutAndSet(usize, T),
    After(usize, Vec<usize>),
    AfterMutAndSet(usize, Vec<usize>, T),
    Before(usize, Vec<usize>),
    BeforeMutAndSet(usize, Vec<usize>, T),
    Push(T),
    Pop,
    PushAndPop(T),
}

fn simulate<T: Eq>(
    operation: Operation<T>,
    simple: &mut simple::Queue,
    complex: &mut hopscotch::Queue,
) -> bool {
    match op {
        Len => return simple.len() == complex.len(),
        Clear => {
            simple.clear();
            complex.clear();
        },
        NextIndex => return simple.next_index() == complex.next_index(),
        FirstIndex => return simple.first_index() == complex.first_index(),
        ShrinkToFit => {
            simple.shrink_to_fit();
            complex.shirnk_to_fit();
        },
        ShrinkAllToFit => {
            simple.shrink_all_to_fit();
            complex.shrink_all_to_fit();
        },
        Get(index) => return simple.get(index) == complex.get(index),
        GetMutAndSet(index, new) => {
            let (simple_ref, complex_ref) =
                (simple.get_mut(index), complex.get_mut(index));
            if simple_ref != complex_ref {
                return false;
            }
            *simple_ref = new;
            *complex_ref = new;
        },
        After(index, tags) =>
            return simple.after(index, tags) == complex.after(index, tags),
        AfterMutAndSet(index, tags, new) => {
            let (simple_ref, complex_ref) =
                (simple.after_mut(index, taqgs),
                 complex.after_mut(index, tags));
            if simple_ref != complex_ref {
                return false;
            }
            *simple_ref = new;
            *complex_ref = new;
        },
        Before(usize, Vec<usize>),
        BeforeMutAndSet(usize, Vec<usize>, T),
        Push(T),
        Pop,
        PushAndPop(T),
    }
    true
}

/// A simple reference implementation of the same functionality as a hopscotch
/// queue, with worse asymptotics.
mod simple {
    use std::convert::TryInto;
    use std::collections::VecDeque;
    use hopscotch::Item;

    /// A simple queue which should be behaviorally indistinguishable (but
    /// slower) than a hopscotch queue. Used for testing by bi-simulation.
    struct Queue<T> {
        offset: u64,
        inner: VecDeque<(usize, T)>
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
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag) {
                    return Some(item)
                }
                index += 1;
            }
        }

        pub fn after_mut(&mut self, mut index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag) {
                    break;
                }
                index += 1;
            }
            self.get_mut(index)
        }

        pub fn before(&self, mut index: u64, tags: &[usize]) -> Option<Item<&T>> {
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag) {
                    return Some(item)
                }
                index -= 1;
            }
        }

        pub fn before_mut(&mut self, mut index: u64, tags: &[usize]) -> Option<Item<&mut T>> {
            loop {
                let item = self.get(index)?;
                if tags.contains(&item.tag) {
                    break;
                }
                index -= 1;
            }
            self.get_mut(index)
        }

        pub fn push(&mut self, tag: usize, value: T) -> u64 {
            self.inner.push_back((tag, value));
            self.offset + (self.inner.len() as u64)
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
