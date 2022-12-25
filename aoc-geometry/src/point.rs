//! Structs and traits for various points.
//!
//! Points can only contain signed values.
//!
//! For convenience, 2d and 3d points have specialized implementations that
//! expose specific attributes like x, y, z. Higher dimensional points are
//! available, but are generic via array wrappers.
use std::{
    hash::Hash,
    iter::Sum,
    ops::{Add, Deref},
};

use num::{Bounded, Num};

/// A colleciton of basic things that all "points" provide.
pub trait AocPoint {
    type Output: Num;

    /// Calculate the manhattan distance between ourself and an Other.
    fn manhattan_dist(&self, other: &Self) -> Self::Output;
}

/// A point representing something like (x, y).
///
/// # Examples
/// ```
/// use aoc_geometry::Point2D;
/// let p = Point2D::<i64>::default();
/// assert_eq!(p.x, 0_i64);
/// assert_eq!(p.y, 0_i64);
/// ```
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub struct Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub x: T,
    pub y: T,
}

impl<T> Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Make a new Point2D
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Point2D;
    /// let p: Point2D<i64> = Point2D::new(2, 3);
    /// assert_eq!(p.x, 2_i64);
    /// assert_eq!(p.y, 3_i64);
    /// ```
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }

    /// Yield a point that is North of this one.
    ///
    /// We consider North to have a y value one larger.
    pub fn north(&self) -> Self {
        (self.x, self.y + T::one()).into()
    }

    /// Yield a point that is North-east of this one.
    ///
    /// We consider North-east to have an x and y value one larger.
    pub fn north_east(&self) -> Self {
        (self.x + T::one(), self.y + T::one()).into()
    }

    /// Yield a point that is North-west of this one.
    ///
    /// We consider North-west to have an x value one smaller and y value one
    /// larger.
    pub fn north_west(&self) -> Self {
        (self.x - T::one(), self.y + T::one()).into()
    }

    /// Yield a point that is South of this one.
    ///
    /// We consider South to have a y value one smaller.
    pub fn south(&self) -> Self {
        (self.x, self.y - T::one()).into()
    }

    /// Yield a point that is South-east of this one.
    ///
    /// We consider South-east to have an x value one larger and a y value one
    /// smaller.
    pub fn south_east(&self) -> Self {
        (self.x + T::one(), self.y - T::one()).into()
    }

    /// Yield a point that is South-west of this one.
    ///
    /// We consider South-west to have an x and y value one smaller.
    pub fn south_west(&self) -> Self {
        (self.x - T::one(), self.y - T::one()).into()
    }

    /// Yield a point that is East of this one.
    ///
    /// We consider East to have an x value one larger.
    pub fn east(&self) -> Self {
        (self.x + T::one(), self.y).into()
    }

    /// Yield a point that is West of this one.
    ///
    /// We consider West to have an x value one smaller.
    pub fn west(&self) -> Self {
        (self.x - T::one(), self.y).into()
    }
}

impl<T> From<(T, T)> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (T, T)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl<T> Add<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: Point2D<T>) -> Self::Output {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<T> AocPoint for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = T;

    fn manhattan_dist(&self, other: &Self) -> Self::Output {
        // this is not as efficient, but it satisfies both signed and unsigned
        // values
        (self.x.max(other.x) - self.x.min(other.x)) + (self.y.max(other.y) - self.y.min(other.y))
    }
}

/// A point representing something like (x, y, z).
///
/// # Examples
/// ```
/// use aoc_geometry::Point3D;
/// let p = Point3D::<i64>::default();
/// assert_eq!(p.x, 0_i64);
/// assert_eq!(p.y, 0_i64);
/// assert_eq!(p.z, 0_i64);
/// ```
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub struct Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub x: T,
    pub y: T,
    pub z: T,
}

impl<T> Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Make a new Point3D
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Point3D;
    /// let p: Point3D<i64> = Point3D::new(2, 3, 4);
    /// assert_eq!(p.x, 2_i64);
    /// assert_eq!(p.y, 3_i64);
    /// assert_eq!(p.z, 4_i64);
    /// ```
    pub fn new(x: T, y: T, z: T) -> Self {
        Self { x, y, z }
    }
}

impl<T> From<(T, T, T)> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (T, T, T)) -> Self {
        Self::new(value.0, value.1, value.2)
    }
}

impl<T> Add<Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn add(self, rhs: Point3D<T>) -> Self::Output {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl<T> AocPoint for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = T;

    fn manhattan_dist(&self, other: &Self) -> Self::Output {
        // this is not as efficient, but it satisfies both signed and unsigned
        // values
        (self.x.max(other.x) - self.x.min(other.x))
            + (self.y.max(other.y) - self.y.min(other.y))
            + (self.z.max(other.z) - self.z.min(other.z))
    }
}

/// A point of a numberic type comprised of N values.
///
/// # Examples
/// ```
/// use aoc_geometry::PointND;
/// let p1 = PointND::<4, i64>::default();
/// // or from a fixed length array
/// let p2 = PointND::from([1_i32, 2, 3]);
///
/// // and some special tuple cases
/// let p3 = PointND::from((1_u64, 2, 3, 4, 5));
/// ```
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct PointND<const N: usize, T>(pub [T; N])
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash;

impl<const N: usize, T> PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Make a new PointND from the given values.
    pub fn new(values: [T; N]) -> Self {
        Self(values)
    }
}

impl<const N: usize, T> Default for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn default() -> Self {
        Self([T::default(); N])
    }
}

impl<const N: usize, T> Deref for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Target = [T; N];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize, T> AocPoint for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash + Sum,
{
    type Output = T;

    fn manhattan_dist(&self, other: &Self) -> Self::Output {
        self.0
            .iter()
            .zip(other.0.iter())
            .map(|(a, b)| *a.max(b) - *a.min(b))
            .sum()
    }
}

impl<const N: usize, T> From<[T; N]> for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: [T; N]) -> Self {
        Self(value)
    }
}

// special cases
impl<T> From<(T, T, T, T)> for PointND<4, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (T, T, T, T)) -> Self {
        Self::new([value.0, value.1, value.2, value.3])
    }
}

impl<T> From<(T, T, T, T, T)> for PointND<5, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (T, T, T, T, T)) -> Self {
        Self::new([value.0, value.1, value.2, value.3, value.4])
    }
}

/// Locations are special (row, colum) points mainly used as indexes into grids.
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub struct Location {
    row: usize,
    col: usize,
}

impl Location {
    pub fn new(row: usize, col: usize) -> Self {
        Self { row, col }
    }

    /// Attempt to get a location that would be North of this one.
    ///
    /// We consider North to be a _lower_ row.
    ///
    /// This returns `None` if row is 0.
    pub fn north(&self) -> Option<Self> {
        if self.row == 0 {
            None
        } else {
            Some((self.row - 1, self.col).into())
        }
    }

    /// Attempt to get a location that would be South of this one.
    ///
    /// We consider South to be a _higher_ row.
    ///
    /// This _always_ returns a value.
    pub fn south(&self) -> Option<Self> {
        Some((self.row + 1, self.col).into())
    }

    /// Attempt to get a location that would be East of this one.
    ///
    /// We consider East to be a _higher_ col.
    ///
    /// This _always_ returns a value.
    pub fn east(&self) -> Option<Self> {
        Some((self.row, self.col + 1).into())
    }

    /// Attempt to get a location that would be West of this one.
    ///
    /// We consider West to be a _lower_ col.
    ///
    /// This returns `None` if col is 0
    pub fn west(&self) -> Option<Self> {
        if self.col == 0 {
            None
        } else {
            Some((self.row, self.col - 1).into())
        }
    }
}

impl From<(usize, usize)> for Location {
    fn from(value: (usize, usize)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl AocPoint for Location {
    type Output = usize;

    fn manhattan_dist(&self, other: &Self) -> Self::Output {
        self.row.abs_diff(other.row) + self.col.abs_diff(other.col)
    }
}

#[cfg(test)]
mod tests {
    #[allow(non_snake_case)]
    mod Point2D {
        use super::super::*;

        #[test]
        fn construction() {
            let p1 = Point2D::new(2, 3);
            let p2: Point2D<i64> = (2, 3).into();
            assert_eq!(p1, p2);
        }

        #[test]
        fn manhattan_dist() {
            let p1 = Point2D::new(2_u16, 3);
            let p2 = Point2D::new(5_u16, 7);
            assert_eq!(p1.manhattan_dist(&p2), 7);
            assert_eq!(p2.manhattan_dist(&p1), 7);
        }

        #[test]
        fn north() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(0, 1);

            assert_eq!(p.north(), expected);
        }

        #[test]
        fn north_east() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(1, 1);

            assert_eq!(p.north_east(), expected);
        }

        #[test]
        fn north_west() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(-1, 1);

            assert_eq!(p.north_west(), expected);
        }

        #[test]
        fn south() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(0, -1);

            assert_eq!(p.south(), expected);
        }

        #[test]
        fn south_east() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(1, -1);

            assert_eq!(p.south_east(), expected);
        }

        #[test]
        fn south_west() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(-1, -1);

            assert_eq!(p.south_west(), expected);
        }

        #[test]
        fn east() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(1, 0);

            assert_eq!(p.east(), expected);
        }

        #[test]
        fn west() {
            let p: Point2D<i32> = Point2D::default();
            let expected = Point2D::new(-1, 0);

            assert_eq!(p.west(), expected);
        }
    }

    #[allow(non_snake_case)]
    mod Point3D {
        use super::super::*;

        #[test]
        fn construction() {
            let p1 = Point3D::new(2, 3, 4);
            let p2: Point3D<i64> = (2, 3, 4).into();
            assert_eq!(p1, p2);
        }

        #[test]
        fn manhattan_dist() {
            let p1 = Point3D::new(2_u16, 3, 20);
            let p2 = Point3D::new(5_u16, 7, 6);
            assert_eq!(p1.manhattan_dist(&p2), 21);
            assert_eq!(p2.manhattan_dist(&p1), 21);
        }
    }

    #[allow(non_snake_case)]
    mod PointND {
        use super::super::*;

        #[test]
        fn construction() {
            let p1 = PointND::new([2, 3, 4, 5]);
            let p2 = PointND::from([2, 3, 4, 5]);
            let p3: PointND<4, i64> = (2, 3, 4, 5).into();
            assert_eq!(p1, p2);
            assert_eq!(p1, p3);
        }

        #[test]
        fn manhattan_dist() {
            let p1 = PointND::new([2_u16, 3, 20, 4]);
            let p2 = PointND::new([5_u16, 7, 6, 1]);
            assert_eq!(p1.manhattan_dist(&p2), 24);
            assert_eq!(p2.manhattan_dist(&p1), 24);
        }
    }

    #[allow(non_snake_case)]
    mod Location {
        use super::super::*;

        #[test]
        fn manhattan_dist() {
            let p1 = Location::new(1, 3);
            let p2 = Location::new(7, 1);
            assert_eq!(p1.manhattan_dist(&p2), 8);
            assert_eq!(p2.manhattan_dist(&p1), 8);
        }

        #[test]
        fn north() {
            let p = Location::default();
            assert_eq!(p.north(), Option::None);

            let p = Location::new(12, 6);
            let expected = Location::new(11, 6);
            assert_eq!(p.north(), Some(expected));
        }

        #[test]
        fn south() {
            let p = Location::new(12, 6);
            let expected = Location::new(13, 6);
            assert_eq!(p.south(), Some(expected));
        }

        #[test]
        fn east() {
            let p = Location::new(12, 6);
            let expected = Location::new(12, 7);
            assert_eq!(p.east(), Some(expected));
        }

        #[test]
        fn west() {
            let p = Location::default();
            assert_eq!(p.west(), Option::None);

            let p = Location::new(12, 6);
            let expected = Location::new(12, 5);
            assert_eq!(p.west(), Some(expected));
        }
    }
}
