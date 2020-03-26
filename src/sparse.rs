use std::iter;
use std::slice;
use std::vec;

#[derive(Debug, Clone)]
pub struct Sparse<T> {
    end: usize,
    indices: Vec<usize>,
    values: Vec<T>,
}

impl<T> Sparse<T> {
    pub fn new() -> Sparse<T> {
        Self::with_capacity(0)
    }

    pub fn with_capacity(capacity: usize) -> Sparse<T> {
        Sparse {
            end: 0,
            indices: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
        }
    }

    pub fn push(&mut self, value: T) {
        self.indices.push(self.end);
        self.values.push(value);
        self.end = self.end.checked_add(1).expect("Sparse::push: overflow")
    }

    pub fn pop(&mut self) -> Option<T> {
        self.end = self.end.saturating_sub(1);
        if let Some(i) = self.indices.last() {
            if *i == self.end {
                self.indices.pop();
                self.values.pop()
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn skip(&mut self, distance: usize) {
        self.end = self.end.checked_add(distance).expect("Sparse::skip: overflow")
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.values.get(self.indices.binary_search(&index).ok()?)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.values.get_mut(self.indices.binary_search(&index).ok()?)
    }

    pub fn clear(&mut self) {
        self.indices.clear();
        self.values.clear();
        self.end = 0;
    }

    pub fn count(&self) -> usize {
        self.indices.len()
    }

    pub fn len(&self) -> usize {
        self.end
    }

    pub fn iter(&self) -> Iter<T> {
        Iter { inner: self.indices.iter().copied().zip(self.values.iter()) }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut { inner: self.indices.iter().copied().zip(self.values.iter_mut()) }
    }

    pub fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.indices.iter().copied()
    }

    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.values.iter()
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.values.iter_mut()
    }

    pub fn shrink_to_fit(&mut self) {
        self.indices.shrink_to_fit();
        self.values.shrink_to_fit();
    }

    pub fn into_dense(self) -> Vec<T> where T: Default {
        self.into_dense_with(|_, v| v.unwrap_or(T::default()))
    }

    pub fn into_dense_with_default(self, default: T) -> Vec<T> where T: Clone {
        self.into_dense_with(|_, v| v.unwrap_or(default.clone()))
    }

    pub fn into_dense_with<S>(self, f: impl Fn(usize, Option<T>) -> S) -> Vec<S> {
        let length = self.len();
        let mut result = Vec::with_capacity(self.len());
        let mut i_prev = None;
        // The main part
        for (i, v) in self.into_iter() {
            for j in i_prev.unwrap_or(0) .. i {
                result.push(f(j, None));
            }
            result.push(f(i, Some(v)));
            i_prev = Some(i + 1);
        }
        // The trailing end
        for j in i_prev.unwrap_or(0) .. length {
            result.push(f(j, None));
        }
        result
    }
}

// Iterating over `&T`

pub struct Iter<'a, T> {
    inner: iter::Zip<std::iter::Copied<slice::Iter<'a, usize>>, slice::Iter<'a, T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a Sparse<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// Iterating over `&mut T`

pub struct IterMut<'a, T> {
    inner: iter::Zip<std::iter::Copied<slice::Iter<'a, usize>>, slice::IterMut<'a, T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> IntoIterator for &'a mut Sparse<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// Iterating over `T`

pub struct IntoIter<T> {
    inner: iter::Zip<vec::IntoIter<usize>, vec::IntoIter<T>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (usize, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> IntoIterator for Sparse<T> {
    type Item = (usize, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { inner: self.indices.into_iter().zip(self.values.into_iter()) }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::{quickcheck, Arbitrary, Gen};

    // We use random simulation testing to check that the operations over sparse
    // vectors correspond to equivalent operations over normal vectors of
    // `Option`.

    #[derive(Debug, Clone)]
    enum Operation<T> {
        Push(T),
        Pop,
        Skip(usize),
        Get(usize),
        GetMutAndSet(usize, T),
        Clear,
        Count,
        Len,
        Values,
        ValuesMutAndSet(Vec<(usize, T)>),
        Indices,
        Iter,
        IterMutAndSet(Vec<(usize, T)>),
        ShrinkToFit,
        Equal,
    }

    impl<T: Arbitrary> Arbitrary for Operation<T> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            use Operation::*;
            match usize::arbitrary(g) % 15 {
                0 => Push(T::arbitrary(g)),
                1 => Pop,
                2 => Skip(usize::arbitrary(g)),
                3 => Get(usize::arbitrary(g)),
                4 => GetMutAndSet(usize::arbitrary(g), T::arbitrary(g)),
                5 => Clear,
                6 => Count,
                7 => Len,
                8 => Values,
                9 => ValuesMutAndSet(Vec::arbitrary(g)),
                10 => Indices,
                11 => Iter,
                12 => IterMutAndSet(Vec::arbitrary(g)),
                13 => ShrinkToFit,
                14 => Equal,
                _ => panic!("Bad discriminant while generating operation!")
            }
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            use Operation::*;
            match self {
                Push(v) => Box::new(v.shrink().map(Push)),
                Pop => Box::new(iter::empty()),
                Skip(gap) => Box::new(gap.shrink().map(Skip)),
                Get(index) => Box::new(index.shrink().map(Get)),
                GetMutAndSet(index, new) => {
                    Box::new((index.clone(), new.clone())
                            .shrink().map(|(i, n)| GetMutAndSet(i, n)))
                },
                Clear => Box::new(iter::empty()),
                Count => Box::new(iter::empty()),
                Len => Box::new(iter::empty()),
                Values => Box::new(iter::empty()),
                ValuesMutAndSet(news) =>
                    Box::new(news.shrink().map(ValuesMutAndSet)),
                Indices => Box::new(iter::empty()),
                Iter => Box::new(iter::empty()),
                IterMutAndSet(news) => Box::new(news.shrink().map(IterMutAndSet)),
                ShrinkToFit => Box::new(iter::empty()),
                Equal => Box::new(iter::empty()),
            }
        }
    }

    /// Step the simulation forward by applying the given operation to both the
    /// sparse vector and its reference implementation. Returns `false` if there
    /// is a mismatch in the result of an operation.
    fn simulation_step<T: Clone + Eq>(
        o: Operation<T>,
        s: &mut Sparse<T>,
        v: &mut Vec<Option<T>>
    ) -> bool {
        use Operation::*;
        match o {
            Push(val) => {
                s.push(val.clone());
                v.push(Some(val));
                true
            },
            Pop => s.pop() == v.pop().unwrap_or(None),
            Skip(gap) => {
                s.skip(gap);
                for _ in 0 .. gap {
                    v.push(None);
                }
                true
            },
            Get(i) => s.get(i) == v.get(i).unwrap_or(&None).as_ref(),
            GetMutAndSet(i, new) => {
                let x: Option<&mut T> =
                    if let Some(Some(x)) = v.get_mut(i) {
                        Some(x)
                    } else {
                        None
                    };
                let y: Option<&mut T> = s.get_mut(i);
                let equal_before = x == y;
                match (x, y) {
                    (Some(x), Some(y)) => {
                        *x = new.clone();
                        *y = new;
                        let equal_after = x == y;
                        equal_before && equal_after
                    },
                    (None, None) => equal_before,
                    _ => false,
                }
            },
            Clear => {
                v.clear();
                s.clear();
                true
            },
            Count => v.iter().filter(|x| x.is_some()).count() == s.count(),
            Len => v.len() == s.len(),
            Iter => {
                let s_values: Vec<(usize, &T)> = s.iter().collect();
                let v_values: Vec<(usize, &T)> =
                    v.iter().enumerate().filter_map(|(i, v)| {
                        if let Some(v) = v { Some((i, v)) } else { None }
                    }).collect();
                s_values == v_values
            },
            IterMutAndSet(news) => {
                let mut s_values: Vec<(usize, &mut T)> =
                    s.iter_mut().collect();
                let mut v_values: Vec<(usize, &mut T)> =
                    v.iter_mut().enumerate().filter_map(|(i, v)| {
                        if let Some(v) = v { Some((i, v)) } else { None }
                    }).collect();
                let equal_before = s_values == v_values;
                for (index, new) in news.clone().into_iter() {
                    if let Some((_, v)) = s_values.get_mut(index) {
                        **v = new;
                    }
                }
                for (index, new) in news.into_iter() {
                    if let Some((_, v)) = v_values.get_mut(index) {
                        **v = new;
                    }
                }
                let equal_after = s_values == v_values;
                equal_before && equal_after
            },
            Values => {
                let s_values: Vec<&T> = s.values().collect();
                let v_values: Vec<&T> =
                    v.iter().filter_map(|v| v.as_ref()).collect();
                s_values == v_values
            },
            ValuesMutAndSet(news) => {
                let mut s_values: Vec<&mut T> =
                    s.values_mut().collect();
                let mut v_values: Vec<&mut T> =
                    v.iter_mut().filter_map(|v| v.as_mut()).collect();
                let equal_before = s_values == v_values;
                for (index, new) in news.clone().into_iter() {
                    if let Some(v) = s_values.get_mut(index) {
                        **v = new;
                    }
                }
                for (index, new) in news.into_iter() {
                    if let Some(v) = v_values.get_mut(index) {
                        **v = new;
                    }
                }
                let equal_after = s_values == v_values;
                equal_before && equal_after
            },
            Indices => {
                let s_indices: Vec<usize> = s.indices().collect();
                let v_indices: Vec<usize> =
                    v.iter().enumerate().filter_map(|(i, v)| {
                        if v.is_some() { Some(i) } else { None }
                    }).collect();
                s_indices == v_indices
            },
            ShrinkToFit => {
                s.shrink_to_fit();
                v.shrink_to_fit();
                true
            },
            Equal => {
                *v == s.clone().into_dense_with(|_, v| v)
            },
        }
    }

    #[test]
    fn empty_is_empty() {
        let v: Vec<usize> = Vec::new();
        let s = Sparse::new();
        assert_eq!(v, s.into_dense(),
                   "Empty sparse vector, when converted to dense, must be empty")
    }

    quickcheck! {
        fn push_sparse_is_push_dense(xs: Vec<usize>) -> bool {
            let mut vec = Vec::with_capacity(xs.len());
            let mut sparse = Sparse::with_capacity(xs.len());
            for x in xs.iter().copied() {
                vec.push(Some(x));
                sparse.push(x);
            }
            let dense = sparse.into_dense_with(|_, v| v);
            vec == dense
        }

        fn skip_sparse_is_push_many_dense(gap: usize, split: usize, xs: Vec<usize>) -> bool {
            let (xs0, xs1) = xs.split_at(split % (xs.len() + 1));
            let mut sparse = Sparse::new();
            let mut vec = Vec::new();
            // Push the first half
            for x in xs0.iter().copied() {
                vec.push(Some(x));
                sparse.push(Some(x));
            }
            // Now skip some
            sparse.skip(gap);
            for _ in 0 .. gap {
                vec.push(None);
            }
            // Push the second half
            for x in xs1.iter().copied() {
                vec.push(Some(x));
                sparse.push(Some(x));
            }
            let dense = sparse.into_dense_with_default(None);
            vec == dense
        }

        fn simulates_dense_vector(operations: Vec<Operation<usize>>) -> bool {
            let mut v = Vec::new();
            let mut s = Sparse::new();
            for o in operations {
                if !simulation_step(o, &mut s, &mut v) {
                    return false;
                }
            }
            true
        }
    }
}
