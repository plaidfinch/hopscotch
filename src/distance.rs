use std::ops::{Add, Sub};

pub const INFINITY: Distance = Distance(usize::max_value());

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Distance(pub usize);

impl std::fmt::Display for Distance {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if *self == INFINITY {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Add<Distance> for Distance {
    type Output = Distance;
    fn add(self, other: Distance) -> Distance {
        Distance(self.0.saturating_add(other.0))
    }
}

impl Add<usize> for Distance {
    type Output = usize;
    fn add(self, other: usize) -> usize {
        self.0.saturating_add(other)
    }
}

impl Add<Distance> for usize {
    type Output = usize;
    fn add(self, other: Distance) -> usize {
        self.saturating_add(other.0)
    }
}

impl Sub<Distance> for Distance {
    type Output = Option<Distance>;
    fn sub(self, other: Distance) -> Option<Distance> {
        if self == INFINITY {
            Some(INFINITY)
        } else {
            let result = self.0.checked_sub(other.0)?;
            Some(Distance(result))
        }
    }
}

impl Sub<Distance> for usize {
    type Output = Option<usize>;
    fn sub(self, other: Distance) -> Option<usize> {
        if other == INFINITY {
            None
        } else {
            self.checked_sub(other.0)
        }
    }
}
