//! Various representations of a boundary.
//!
//! Bounds are primarily used to determine the minimum space taken by a cloud of
//! points, including the minmum and maximum values of the region those points
//! occupy.
//!
//! For convenience 2d and 3d bounds have specialized implementations that
//! expose specific attributes like `min_x` and `max_y`. Higher dimensional
//! bounds are available but are generic via arrays.
use std::{hash::Hash, iter::Product};

use num::{Bounded, Num};
use thiserror::Error;

use crate::{Point2D, Point3D, PointND};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Error)]
#[non_exhaustive]
pub enum BoundError {
    #[error("Specified dimension {got} is below 1 or exceeds the max ({max})")]
    InvalidDimension { got: usize, max: usize },
}

/// A basic set of things all bounds support
pub trait AocBound {
    type PointKind;

    /// Make a new Bound using the min/max attributes from the given two points.
    fn new(p1: &Self::PointKind, p2: &Self::PointKind) -> Self;

    /// Initialize a boundary with min values initialized to MAX and max to MIN.
    ///
    /// Used as a starting state for finding boundaries.
    fn minmax() -> Self;

    /// Checks if the given Point is contained (inclusive) by the bounds.
    fn contains(&self, point: &Self::PointKind) -> bool;

    /// normalize the given point relative to the min corner of the bound.
    fn normalize(&self, point: &Self::PointKind) -> Option<Self::PointKind>;

    /// update the bounds with the given point
    fn update(&mut self, point: &Self::PointKind);
}

/// A two-dimensional boundary.
///
/// # Examples
/// ```
/// use aoc_geometry::Bound2D;
/// ```
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub struct Bound2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub min_x: T,
    pub min_y: T,
    pub max_x: T,
    pub max_y: T,
}

impl<T> Bound2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// The "width" of this bound.
    ///
    /// This corresponds to the range of the x parameters + 1
    pub fn width(&self) -> T {
        self.max_x - self.min_x + T::one()
    }

    /// The "height" of this bound.
    ///
    /// This corresponds to the range of the y parameters + 1
    pub fn height(&self) -> T {
        self.max_y - self.min_y + T::one()
    }

    /// The total area represented by these bounds.
    pub fn area(&self) -> T {
        self.width() * self.height()
    }
}

impl<T> AocBound for Bound2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type PointKind = Point2D<T>;

    fn new(p1: &Self::PointKind, p2: &Self::PointKind) -> Self {
        Self {
            min_x: p1.x.min(p2.x),
            min_y: p1.y.min(p2.y),
            max_x: p1.x.max(p2.x),
            max_y: p1.y.max(p2.y),
        }
    }

    fn minmax() -> Self {
        Self {
            min_x: T::max_value(),
            min_y: T::max_value(),
            max_x: T::min_value(),
            max_y: T::min_value(),
        }
    }

    fn contains(&self, point: &Self::PointKind) -> bool {
        self.min_x <= point.x
            && self.max_x >= point.x
            && self.min_y <= point.y
            && self.max_y >= point.y
    }

    fn normalize(&self, point: &Self::PointKind) -> Option<Self::PointKind> {
        if self.contains(point) {
            Some(Point2D {
                x: point.x - self.min_x,
                y: point.y - self.min_y,
            })
        } else {
            None
        }
    }

    fn update(&mut self, point: &Self::PointKind) {
        self.min_x = self.min_x.min(point.x);
        self.min_y = self.min_y.min(point.y);
        self.max_x = self.max_x.max(point.x);
        self.max_y = self.max_y.max(point.y);
    }
}

impl<T> Bound3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// The "width" of this bound.
    ///
    /// This corresponds to the range of the x parameters + 1
    pub fn width(&self) -> T {
        self.max_x - self.min_x + T::one()
    }

    /// The "height" of this bound.
    ///
    /// This corresponds to the range of the y parameters + 1
    pub fn height(&self) -> T {
        self.max_y - self.min_y + T::one()
    }

    /// The "depth" of this bound.
    ///
    /// This corresponds to the range of the z parameters + 1
    pub fn depth(&self) -> T {
        self.max_z - self.min_z + T::one()
    }

    /// The total volume represented by these bounds.
    pub fn volume(&self) -> T {
        self.width() * self.height() * self.depth()
    }
}

impl<'a, N> FromIterator<&'a Point2D<N>> for Bound2D<N>
where
    N: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from_iter<T: IntoIterator<Item = &'a Point2D<N>>>(iter: T) -> Self {
        let mut bound = Bound2D::minmax();

        for point in iter {
            if bound.min_x > point.x {
                bound.min_x = point.x;
            }

            if bound.max_x < point.x {
                bound.max_x = point.x;
            }

            if bound.min_y > point.y {
                bound.min_y = point.y;
            }

            if bound.max_y < point.y {
                bound.max_y = point.y;
            }
        }

        bound
    }
}

/// A three-dimensional boundary.
///
/// # Examples
/// ```
/// use aoc_geometry::Bound3D;
/// ```
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Hash)]
pub struct Bound3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub min_x: T,
    pub min_y: T,
    pub min_z: T,
    pub max_x: T,
    pub max_y: T,
    pub max_z: T,
}

impl<T> AocBound for Bound3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type PointKind = Point3D<T>;

    fn new(p1: &Self::PointKind, p2: &Self::PointKind) -> Self {
        Self {
            min_x: p1.x.min(p2.x),
            min_y: p1.y.min(p2.y),
            min_z: p1.z.min(p2.z),
            max_x: p1.x.max(p2.x),
            max_y: p1.y.max(p2.y),
            max_z: p1.z.max(p2.z),
        }
    }

    fn minmax() -> Self {
        Self {
            min_x: T::max_value(),
            min_y: T::max_value(),
            min_z: T::max_value(),
            max_x: T::min_value(),
            max_y: T::min_value(),
            max_z: T::min_value(),
        }
    }

    fn contains(&self, point: &Self::PointKind) -> bool {
        self.min_x <= point.x
            && self.max_x >= point.x
            && self.min_y <= point.y
            && self.max_y >= point.y
            && self.min_z <= point.z
            && self.max_z >= point.z
    }

    fn normalize(&self, point: &Self::PointKind) -> Option<Self::PointKind> {
        if self.contains(point) {
            Some(Point3D {
                x: point.x - self.min_x,
                y: point.y - self.min_y,
                z: point.z - self.min_z,
            })
        } else {
            None
        }
    }

    fn update(&mut self, point: &Self::PointKind) {
        self.min_x = self.min_x.min(point.x);
        self.min_y = self.min_y.min(point.y);
        self.min_z = self.min_z.min(point.z);
        self.max_x = self.max_x.max(point.x);
        self.max_y = self.max_y.max(point.y);
        self.max_z = self.max_z.max(point.z);
    }
}

impl<'a, N> FromIterator<&'a Point3D<N>> for Bound3D<N>
where
    N: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from_iter<T: IntoIterator<Item = &'a Point3D<N>>>(iter: T) -> Self {
        let mut bound = Bound3D::minmax();

        for point in iter {
            if bound.min_x > point.x {
                bound.min_x = point.x;
            }

            if bound.max_x < point.x {
                bound.max_x = point.x;
            }

            if bound.min_y > point.y {
                bound.min_y = point.y;
            }

            if bound.max_y < point.y {
                bound.max_y = point.y;
            }

            if bound.min_z > point.z {
                bound.min_z = point.z;
            }

            if bound.max_z < point.z {
                bound.max_z = point.z;
            }
        }

        bound
    }
}

/// A n-dimensional boundary.
///
/// # Examples
/// ```
/// use aoc_geometry::BoundND;
/// ```
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BoundND<const N: usize, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    dimensions: [[T; 2]; N],
}

impl<const N: usize, T> BoundND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash + Product,
{
    /// The length in a particular dimension (index starting at 1).
    ///
    /// This will result in an error if the dimension exceeds the available
    /// deimensions or the dimension is < 1.
    pub fn length(&self, dimension: usize) -> Result<T, BoundError> {
        if dimension > N || dimension < 1 {
            return Err(BoundError::InvalidDimension {
                got: dimension,
                max: N,
            });
        }

        Ok(self.dimensions[dimension][1] - self.dimensions[dimension][0] + T::one())
    }

    pub fn enclosed_space(&self) -> T {
        self.dimensions
            .iter()
            .map(|[min, max]| *max - *min + T::one())
            .product()
    }
}

impl<const N: usize, T> Default for BoundND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn default() -> Self {
        Self {
            dimensions: [[T::zero(); 2]; N],
        }
    }
}

impl<const N: usize, T> AocBound for BoundND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type PointKind = PointND<N, T>;

    fn new(p1: &Self::PointKind, p2: &Self::PointKind) -> Self {
        let mut b = Self::default();

        for i in 0..N {
            b.dimensions[i][0] = p1[i].min(p2[i]);
            b.dimensions[i][1] = p1[i].max(p2[i]);
        }

        b
    }

    fn minmax() -> Self {
        Self {
            dimensions: [[T::max_value(), T::min_value()]; N],
        }
    }

    fn contains(&self, point: &Self::PointKind) -> bool {
        self.dimensions
            .iter()
            .enumerate()
            .all(|(idx, [min, max])| *min <= point[idx] && *max >= point[idx])
    }

    fn normalize(&self, point: &Self::PointKind) -> Option<Self::PointKind> {
        if self.contains(point) {
            let mut new_point = PointND::<N, T>::default();

            for i in 0..N {
                new_point[i] = point[i] - self.dimensions[i][0];
            }

            Some(new_point)
        } else {
            None
        }
    }

    fn update(&mut self, point: &Self::PointKind) {
        for i in 0..N {
            self.dimensions[i][0] = self.dimensions[i][0].min(point[i]);
            self.dimensions[i][1] = self.dimensions[i][1].max(point[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    #[allow(non_snake_case)]
    mod Bound2D {
        use super::super::*;

        #[test]
        fn width() {
            // we can never have a zero-width bounds
            let b: Bound2D<usize> = Bound2D::default();
            assert_eq!(b.width(), 1);
        }

        #[test]
        fn height() {
            // we can never have a zero-height bounds
            let b: Bound2D<usize> = Bound2D::default();
            assert_eq!(b.height(), 1);
        }

        #[test]
        fn area() {
            let b: Bound2D<usize> = Bound2D::default();
            assert_eq!(b.area(), 1);
        }

        #[test]
        fn minmax() {
            let b: Bound2D<i64> = Bound2D::minmax();
            let expected = Bound2D {
                min_x: i64::MAX,
                min_y: i64::MAX,
                max_x: i64::MIN,
                max_y: i64::MIN,
            };
            assert_eq!(b, expected);
        }

        #[test]
        fn from_iter() {
            let points = [
                Point2D::new(1_i64, 2),
                Point2D::new(-6, 7),
                Point2D::new(2, -5),
                Point2D::new(4, 16),
            ];

            let b = Bound2D::from_iter(points.iter());
            let expected = Bound2D {
                min_x: -6_i64,
                min_y: -5,
                max_x: 4,
                max_y: 16,
            };

            assert_eq!(b, expected);
        }
    }

    #[allow(non_snake_case)]
    mod Bound3D {
        use super::super::*;

        #[test]
        fn width() {
            // we can never have a zero-width bounds
            let b: Bound3D<usize> = Bound3D::default();
            assert_eq!(b.width(), 1);
        }

        #[test]
        fn height() {
            // we can never have a zero-height bounds
            let b: Bound3D<usize> = Bound3D::default();
            assert_eq!(b.height(), 1);
        }

        #[test]
        fn depth() {
            let b: Bound3D<usize> = Bound3D::default();
            assert_eq!(b.depth(), 1);
        }

        #[test]
        fn volume() {
            let b: Bound3D<usize> = Bound3D::default();
            assert_eq!(b.volume(), 1);
        }

        #[test]
        fn minmax() {
            let b: Bound3D<i64> = Bound3D::minmax();
            let expected = Bound3D {
                min_x: i64::MAX,
                min_y: i64::MAX,
                min_z: i64::MAX,
                max_x: i64::MIN,
                max_y: i64::MIN,
                max_z: i64::MIN,
            };
            assert_eq!(b, expected);
        }

        #[test]
        fn from_iter() {
            let points = [
                Point3D::new(1_i64, 2, -8),
                Point3D::new(-6, 7, 3),
                Point3D::new(2, -5, -2),
                Point3D::new(4, 16, 7),
            ];

            let b = Bound3D::from_iter(points.iter());
            let expected = Bound3D {
                min_x: -6_i64,
                min_y: -5,
                min_z: -8,
                max_x: 4,
                max_y: 16,
                max_z: 7,
            };

            assert_eq!(b, expected);
        }
    }

    #[allow(non_snake_case)]
    mod BoundND {
        use super::super::*;

        #[test]
        fn minmax() {
            let b: BoundND<4, i64> = BoundND::minmax();
            let expected = BoundND {
                dimensions: [
                    [i64::MAX, i64::MIN],
                    [i64::MAX, i64::MIN],
                    [i64::MAX, i64::MIN],
                    [i64::MAX, i64::MIN],
                ],
            };
            assert_eq!(b, expected);
        }
    }
}
