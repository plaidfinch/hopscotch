use hopscotch::sparse::*;
use quickcheck::{quickcheck, Arbitrary, Gen};
use std::iter;

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
            _ => panic!("Bad discriminant while generating operation!"),
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        use Operation::*;
        match self {
            Push(v) => Box::new(v.shrink().map(Push)),
            Pop => Box::new(iter::empty()),
            Skip(gap) => Box::new(gap.shrink().map(Skip)),
            Get(index) => Box::new(index.shrink().map(Get)),
            GetMutAndSet(index, new) => Box::new(
                (index.clone(), new.clone())
                    .shrink()
                    .map(|(i, n)| GetMutAndSet(i, n)),
            ),
            Clear => Box::new(iter::empty()),
            Count => Box::new(iter::empty()),
            Len => Box::new(iter::empty()),
            Values => Box::new(iter::empty()),
            ValuesMutAndSet(news) => Box::new(news.shrink().map(ValuesMutAndSet)),
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
    v: &mut Vec<Option<T>>,
) -> bool {
    use Operation::*;
    match o {
        Push(val) => {
            s.push(val.clone());
            v.push(Some(val));
            true
        }
        Pop => s.pop() == v.pop().unwrap_or(None),
        Skip(gap) => {
            s.skip(gap);
            for _ in 0..gap {
                v.push(None);
            }
            true
        }
        Get(i) => s.get(i) == v.get(i).unwrap_or(&None).as_ref(),
        GetMutAndSet(i, new) => {
            let x: Option<&mut T> = if let Some(Some(x)) = v.get_mut(i) {
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
                }
                (None, None) => equal_before,
                _ => false,
            }
        }
        Clear => {
            v.clear();
            s.clear();
            true
        }
        Count => v.iter().filter(|x| x.is_some()).count() == s.count(),
        Len => v.len() == s.len(),
        Iter => {
            let s_values: Vec<(usize, &T)> = s.iter().collect();
            let v_values: Vec<(usize, &T)> = v
                .iter()
                .enumerate()
                .filter_map(|(i, v)| if let Some(v) = v { Some((i, v)) } else { None })
                .collect();
            s_values == v_values
        }
        IterMutAndSet(news) => {
            let mut s_values: Vec<(usize, &mut T)> = s.iter_mut().collect();
            let mut v_values: Vec<(usize, &mut T)> = v
                .iter_mut()
                .enumerate()
                .filter_map(|(i, v)| if let Some(v) = v { Some((i, v)) } else { None })
                .collect();
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
        }
        Values => {
            let s_values: Vec<&T> = s.values().collect();
            let v_values: Vec<&T> = v.iter().filter_map(|v| v.as_ref()).collect();
            s_values == v_values
        }
        ValuesMutAndSet(news) => {
            let mut s_values: Vec<&mut T> = s.values_mut().collect();
            let mut v_values: Vec<&mut T> = v.iter_mut().filter_map(|v| v.as_mut()).collect();
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
        }
        Indices => {
            let s_indices: Vec<usize> = s.indices().collect();
            let v_indices: Vec<usize> = v
                .iter()
                .enumerate()
                .filter_map(|(i, v)| if v.is_some() { Some(i) } else { None })
                .collect();
            s_indices == v_indices
        }
        ShrinkToFit => {
            s.shrink_to_fit();
            v.shrink_to_fit();
            true
        }
        Equal => *v == s.clone().into_dense(),
    }
}

#[test]
fn empty_is_empty() {
    let v: Vec<Option<usize>> = Vec::new();
    let s = Sparse::new();
    assert_eq!(
        v,
        s.into_dense(),
        "Empty sparse vector, when converted to dense, must be empty"
    )
}

quickcheck! {
    fn to_from_dense_identity(dense: Vec<Option<usize>>) -> bool {
        let dense_0 = dense.clone();
        println!("input: {:?}", dense_0);
        let sparse: Sparse<usize> = dense.into_iter().collect();
        println!("sparse: {:?}", sparse);
        let dense_1 = sparse.into_dense();
        println!("dense: {:?}", dense_1);
        dense_0 == dense_1
    }

    fn push_sparse_is_push_dense(xs: Vec<usize>) -> bool {
        let mut vec = Vec::with_capacity(xs.len());
        let mut sparse = Sparse::with_capacity(xs.len());
        for x in xs.iter().copied() {
            vec.push(Some(x));
            sparse.push(x);
        }
        // println!("{:?}", sparse);
        let dense = sparse.into_dense();
        // println!("{:?}", dense);
        // println!("{:?}", vec);
        vec == dense
    }

    fn skip_sparse_is_push_many_dense(gap: usize, split: usize, xs: Vec<usize>) -> bool {
        let (xs0, xs1) = xs.split_at(split % (xs.len() + 1));
        let mut sparse = Sparse::new();
        let mut vec: Vec<Option<usize>> = Vec::new();
        // Push the first half
        for x in xs0.iter().copied() {
            vec.push(Some(x));
            sparse.push(x);
        }
        // Now skip some
        sparse.skip(gap);
        for _ in 0 .. gap {
            vec.push(None);
        }
        // Push the second half
        for x in xs1.iter().copied() {
            vec.push(Some(x));
            sparse.push(x);
        }
        let dense = sparse.into_dense();
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
