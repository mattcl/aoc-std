use std::{hash::Hash, iter::Sum};

use num::{Bounded, Num, Signed};

use crate::{AocPoint, Point2D};

/// A polygon specified using [Point2D] verticies.
///
/// This is restricted to types that are signed to avoid having to handle
/// winding differences.
///
/// Certain methods will only work for polygons where verticies are only square
/// angles.
///
/// For simplicity, the internal representation will ensure that the last vertex
/// is in the list is equal to the first, appending the first element if
/// necessary.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Polygon<T>
where
    T: Num + Signed + Bounded + Ord + PartialOrd + Copy + Default + Hash + Sum,
{
    pub verticies: Vec<Point2D<T>>,
}

impl<T> Polygon<T>
where
    T: Num + Signed + Bounded + Ord + PartialOrd + Copy + Default + Hash + Sum,
{
    /// Return a new polygon using the specified verticies.
    pub fn new(verticies: Vec<Point2D<T>>) -> Self {
        let mut verticies = verticies;
        if verticies[0] != verticies[verticies.len() - 1] {
            verticies.push(verticies[0]);
        }
        Self { verticies }
    }

    pub fn shoelace_area(&self) -> T {
        let two = T::one() + T::one();
        self.verticies
            .as_slice()
            .windows(2)
            .map(|window| window[0].y * window[1].x - window[0].x * window[1].y)
            .sum::<T>()
            .abs()
            / two
    }

    pub fn perimeter(&self) -> T {
        self.verticies
            .as_slice()
            .windows(2)
            .map(|window| window[0].manhattan_dist(&window[1]))
            .sum()
    }

    pub fn verticies(&self) -> &[Point2D<T>] {
        &self.verticies
    }
}

impl<T> From<Vec<Point2D<T>>> for Polygon<T>
where
    T: Num + Signed + Bounded + Ord + PartialOrd + Copy + Default + Hash + Sum,
{
    fn from(value: Vec<Point2D<T>>) -> Self {
        Self::new(value)
    }
}

impl<T> FromIterator<Point2D<T>> for Polygon<T>
where
    T: Num + Signed + Bounded + Ord + PartialOrd + Copy + Default + Hash + Sum,
{
    fn from_iter<I: IntoIterator<Item = Point2D<T>>>(iter: I) -> Self {
        let verticies = iter.into_iter().collect();
        Self::new(verticies)
    }
}
