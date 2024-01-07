use std::hash::Hash;

use aoc_geometry::{AocBound, Bound2D, Point2D};
use num::{Bounded, Num, ToPrimitive};

/// A grid is a two-dimensional collection of `T`, optionally indexed by [Point2D<T>].
///
/// This works by translating the indexing points via a bounds struct.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct PointGrid<P, T>
where
    P: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub values: Vec<Vec<T>>,
    pub bounds: Bound2D<P>,
}

impl<P, T> PointGrid<P, T>
where
    T: Default + Clone,
    P: Num + Bounded + ToPrimitive + Ord + PartialOrd + Copy + Default + Hash,
{
    pub fn new(bounds: Bound2D<P>) -> Self {
        Self {
            bounds,
            values: vec![
                vec![T::default(); bounds.width().to_usize().unwrap()];
                bounds.height().to_usize().unwrap()
            ],
        }
    }

    pub fn get(&self, point: &Point2D<P>) -> Option<&T> {
        if let Some(Point2D { x, y }) = self.bounds.normalize(point) {
            if let (Some(col), Some(row)) = (x.to_usize(), y.to_usize()) {
                return self.values.get(row).and_then(|r| r.get(col));
            }
        }
        None
    }

    pub fn get_mut(&mut self, point: &Point2D<P>) -> Option<&mut T> {
        if let Some(Point2D { x, y }) = self.bounds.normalize(point) {
            if let (Some(col), Some(row)) = (x.to_usize(), y.to_usize()) {
                return self.values.get_mut(row).and_then(|r| r.get_mut(col));
            }
        }
        None
    }

    pub fn width(&self) -> usize {
        self.bounds.width().to_usize().unwrap()
    }

    pub fn height(&self) -> usize {
        self.bounds.width().to_usize().unwrap()
    }
}
