use std::hash::Hash;

use num::{Bounded, Num};

use crate::Intersect;

/// An interval representing an ordered range from start..=end.
///
/// The sort order of intervals is comparing start then end.
///
/// # Examples
/// ```
/// use aoc_geometry::Interval;
/// let i = Interval::new(-1, 54);
/// assert!(i.contains_value(15));
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub start: T,
    pub end: T,
}

impl<T> Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Make a new interval from `min(start, end)..=max(start, end)`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// let i = Interval::new(5_i64, -1);
    /// assert_eq!(i.start, -1);
    /// assert_eq!(i.end, 5);
    ///
    /// ```
    pub fn new(start: T, end: T) -> Self {
        Self {
            start: start.min(end),
            end: start.max(end),
        }
    }

    /// Get the width of this interval (end - start + 1).
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// let i = Interval::new(5_i64, 27);
    /// assert_eq!(i.width(), 23);
    /// ```
    pub fn width(&self) -> T {
        self.end - self.start + T::one()
    }

    /// Returns true if `self` contains the `value`.
    pub fn contains_value(&self, value: T) -> bool {
        self.start <= value && value <= self.end
    }

    /// Return true if `self` overlaps `other` in any way.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// // self:   ssssssssss
    /// // other:   ooooo
    /// let s = Interval::new(1, 15);
    /// let o = Interval::new(2, 14);
    /// assert!(s.overlaps(&o));
    ///
    /// // self:   ssssssssss
    /// // other:         ooooo
    /// let s = Interval::new(1, 15);
    /// let o = Interval::new(8, 18);
    /// assert!(s.overlaps(&o));
    ///
    /// // self:      ssssssss
    /// // other:  ooooo
    /// let s = Interval::new(4, 15);
    /// let o = Interval::new(0, 8);
    /// assert!(s.overlaps(&o));
    ///
    /// // self:    ssssss
    /// // other:  oooooooo
    /// let s = Interval::new(4, 15);
    /// let o = Interval::new(3, 16);
    /// assert!(s.overlaps(&o));
    ///
    /// // self:         ssssss
    /// // other:  ooooo
    /// let s = Interval::new(4, 15);
    /// let o = Interval::new(1, 3);
    /// assert!(!s.overlaps(&o));
    ///
    /// // self:   ssssss
    /// // other:        ooooo
    /// let s = Interval::new(4, 15);
    /// let o = Interval::new(16, 21);
    /// assert!(!s.overlaps(&o));
    /// ```
    pub fn overlaps(&self, other: &Self) -> bool {
        self.contains(other)
            || self.is_contained_by(other)
            || self.right_of_and_overlaps(other)
            || self.left_of_and_overlaps(other)
    }

    /// Return true if `self` entirely contains `other`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// // self:   ssssssssss
    /// // other:   ooooo
    /// let s = Interval::new(1, 15);
    ///
    /// let o = Interval::new(1, 2);
    /// assert!(s.contains(&o));
    ///
    /// let o = Interval::new(4, 10);
    /// assert!(s.contains(&o));
    ///
    /// let o = Interval::new(10, 15);
    /// assert!(s.contains(&o));
    ///
    /// let o = Interval::new(10, 16);
    /// assert!(!s.contains(&o));
    ///
    /// let o = Interval::new(-2, 16);
    /// assert!(!s.contains(&o));
    /// ```
    pub fn contains(&self, other: &Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    /// Return true if `self` is entirely contained by `other`.
    ///
    /// Unlike contains, this check is exclusive in that
    /// `self.start > other.start` and `self.end < other.end`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// // self:    ssss
    /// // other:  oooooo
    /// let s = Interval::new(1, 15);
    ///
    /// let o = Interval::new(0, 16);
    /// assert!(s.is_contained_by(&o));
    ///
    /// let o = Interval::new(1, 16);
    /// assert!(!s.is_contained_by(&o));
    ///
    /// let o = Interval::new(0, 15);
    /// assert!(!s.is_contained_by(&o));
    ///
    /// let o = Interval::new(22, 26);
    /// assert!(!s.is_contained_by(&o));
    /// ```
    pub fn is_contained_by(&self, other: &Self) -> bool {
        other.start < self.start && self.end < other.end
    }

    /// Return true if `self` is to the left of and overlaps `other`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// // self:   ssssss
    /// // other:     ooooo
    /// let s = Interval::new(1, 15);
    ///
    /// let o = Interval::new(6, 16);
    /// assert!(s.left_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(1, 16);
    /// assert!(s.left_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(10, 14);
    /// assert!(!s.left_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(16, 17);
    /// assert!(!s.left_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(2, 7);
    /// assert!(!s.left_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(1, 15);
    /// assert!(!s.left_of_and_overlaps(&o));
    /// ```
    pub fn left_of_and_overlaps(&self, other: &Self) -> bool {
        self.start <= other.start && other.start <= self.end && self.end < other.end
    }

    /// Return true if `self` is to the right of and overlaps `other`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// // self:     ssssss
    /// // other: ooooo
    /// let s = Interval::new(4, 15);
    ///
    /// let o = Interval::new(0, 8);
    /// assert!(s.right_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(3, 11);
    /// assert!(s.right_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(16, 17);
    /// assert!(!s.right_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(0, 3);
    /// assert!(!s.right_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(4, 16);
    /// assert!(!s.right_of_and_overlaps(&o));
    ///
    /// let o = Interval::new(4, 15);
    /// assert!(!s.right_of_and_overlaps(&o));
    /// ```
    pub fn right_of_and_overlaps(&self, other: &Self) -> bool {
        other.start < self.start && self.start <= other.end && other.end <= self.end
    }

    /// Partition `self` using `other`.
    ///
    /// This returns an [IntervalPartition] containing the partitioned
    /// intervals, if any.
    ///
    /// There are five scenarios:
    ///
    /// # `self` has no overlap with `other`
    /// ```
    /// use aoc_geometry::{Interval, IntervalPartition};
    ///
    /// let s = Interval::new(4, 10);
    /// let o = Interval::new(11, 15);
    ///
    /// assert_eq!(
    ///     s.partition_by(&o),
    ///     IntervalPartition::NoOverlap
    /// );
    /// ```
    ///
    /// # `self` is enitrely contained by `other`
    /// ```
    /// use aoc_geometry::{Interval, IntervalPartition};
    ///
    /// let s = Interval::new(4, 10);
    /// let o = Interval::new(2, 15);
    ///
    /// assert_eq!(
    ///     s.partition_by(&o),
    ///     IntervalPartition::EntirelyContained { overlap: s }
    /// );
    /// ```
    ///
    /// # `self` is to the left of and overlaps `other`
    /// ```
    /// use aoc_geometry::{Interval, IntervalPartition};
    ///
    /// let s = Interval::new(4, 10);
    /// let o = Interval::new(7, 15);
    ///
    /// let left = Interval::new(4, 6);
    /// let overlap = Interval::new(7, 10);
    ///
    /// assert_eq!(
    ///     s.partition_by(&o),
    ///     IntervalPartition::RemainderLeft { left, overlap }
    /// );
    /// ```
    ///
    /// # `self` is to the right of and overlaps `other`
    /// ```
    /// use aoc_geometry::{Interval, IntervalPartition};
    ///
    /// let s = Interval::new(4, 10);
    /// let o = Interval::new(0, 8);
    ///
    /// let overlap = Interval::new(4, 8);
    /// let right = Interval::new(9, 10);
    ///
    /// assert_eq!(
    ///     s.partition_by(&o),
    ///     IntervalPartition::RemainderRight { overlap, right }
    /// );
    /// ```
    ///
    /// # `self` entirely contains `other`
    /// ```
    /// use aoc_geometry::{Interval, IntervalPartition};
    ///
    /// let s = Interval::new(4, 10);
    /// let o = Interval::new(5, 8);
    ///
    /// let left = Interval::new(4, 4);
    /// let overlap = Interval::new(5, 8);
    /// let right = Interval::new(9, 10);
    ///
    /// assert_eq!(
    ///     s.partition_by(&o),
    ///     IntervalPartition::Bisecting { left, overlap, right }
    /// );
    /// ```
    pub fn partition_by(&self, other: &Self) -> IntervalPartition<T> {
        if other.contains(self) {
            IntervalPartition::EntirelyContained { overlap: *self }
        } else if other.right_of_and_overlaps(self) {
            let left = Self {
                start: self.start,
                end: other.start - T::one(),
            };
            let overlap = Self {
                start: other.start,
                end: self.end,
            };
            IntervalPartition::RemainderLeft { left, overlap }
        } else if other.left_of_and_overlaps(self) {
            let overlap = Self {
                start: self.start,
                end: other.end,
            };
            let right = Self {
                start: other.end + T::one(),
                end: self.end,
            };
            IntervalPartition::RemainderRight { overlap, right }
        } else if other.is_contained_by(self) {
            let left = Self {
                start: self.start,
                end: other.start - T::one(),
            };
            let overlap = Self {
                start: other.start,
                end: other.end,
            };
            let right = Self {
                start: other.end + T::one(),
                end: self.end,
            };
            IntervalPartition::Bisecting {
                left,
                overlap,
                right,
            }
        } else {
            IntervalPartition::NoOverlap
        }
    }

    /// Return an interval made from moving `self.start` and `self.end` by
    /// `distance`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Interval;
    ///
    /// let i = Interval::new(1, 3);
    /// let e = Interval::new(12, 14);
    ///
    /// assert_eq!(i.translate(11), e);
    ///
    /// ```
    pub fn translate(&self, distance: T) -> Self {
        Self {
            start: self.start + distance,
            end: self.end + distance,
        }
    }

    /// Split `self` using `value_inclusive`.
    ///
    /// If a split occurs, the left interval will contain `value_inclusive`.
    pub fn split_at(&self, value_inclusive: T) -> IntervalSplit<T> {
        if self.end < value_inclusive {
            IntervalSplit::Left { value: *self }
        } else if self.start > value_inclusive {
            IntervalSplit::Right { value: *self }
        } else {
            IntervalSplit::Bisecting {
                left: Self::new(self.start, value_inclusive),
                right: Self::new(value_inclusive + T::one(), self.end),
            }
        }
    }
}

impl<T> Intersect for Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Intersection = Self;

    fn intersection(&self, other: &Self) -> Option<Self::Intersection> {
        if self.end < other.start || self.start > other.end {
            return None;
        }

        Some(Self {
            start: self.start.max(other.start),
            end: self.end.min(other.end),
        })
    }
}

impl<T> From<(T, T)> for Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (T, T)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl<T> Ord for Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.start
            .cmp(&other.start)
            .then_with(|| self.end.cmp(&other.end))
    }
}

impl<T> PartialOrd for Interval<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A representaiton of the result of partitioning an [Interval].
///
/// See [Interval::partition_by] for more information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntervalPartition<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    NoOverlap,
    EntirelyContained {
        overlap: Interval<T>,
    },
    RemainderLeft {
        left: Interval<T>,
        overlap: Interval<T>,
    },
    RemainderRight {
        overlap: Interval<T>,
        right: Interval<T>,
    },
    Bisecting {
        left: Interval<T>,
        overlap: Interval<T>,
        right: Interval<T>,
    },
}

/// A representaiton of the result of splitting an [Interval].
///
/// See [Interval::split_at] for more information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntervalSplit<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    Left {
        value: Interval<T>,
    },
    Right {
        value: Interval<T>,
    },
    Bisecting {
        left: Interval<T>,
        right: Interval<T>,
    },
}
