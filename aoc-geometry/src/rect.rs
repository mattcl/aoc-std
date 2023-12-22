//! This module contains various definitions for rectangles.
use std::{fmt::Display, hash::Hash};

use num::{Bounded, Num};

use crate::{Intersect, Point2D};

/// A rectangle inclusively defined by two [Point2D] opposite corners.
///
/// The specified corners can be in any order as long as they are opposite.
///
/// The internal representation is guaranteed to be normalized such that
/// `p1.x < p2.x` and `p1.y < p2.y`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    p1: Point2D<T>,
    p2: Point2D<T>,
}

impl<T> Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Create a rectangle from the specified points, which should represent
    /// opposite corners.
    pub fn new(p1: Point2D<T>, p2: Point2D<T>) -> Self {
        (p1, p2).into()
    }

    /// Create a rectangle from x and y values instead of from points.
    ///
    /// The rectangle will be normalized.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::{Rectangle, Point2D};
    ///
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 11);
    /// let expected = Rectangle::from(
    ///    (Point2D::new(0, 1), Point2D::new(10, 11))
    /// );
    ///
    /// assert_eq!(rect, expected);
    /// ```
    pub fn from_raw(x1: T, y1: T, x2: T, y2: T) -> Self {
        Self {
            p1: (x1.min(x2), y1.min(y2)).into(),
            p2: (x1.max(x2), y1.max(y2)).into(),
        }
    }

    /// Get the smaller point of this rectangle.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::{Rectangle, Point2D};
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 11);
    ///
    /// assert_eq!(rect.p1(), &Point2D::new(0, 1));
    /// ```
    pub fn p1(&self) -> &Point2D<T> {
        &self.p1
    }

    /// Get the larger point of this rectangle.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::{Rectangle, Point2D};
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 11);
    ///
    /// assert_eq!(rect.p2(), &Point2D::new(10, 11));
    /// ```
    pub fn p2(&self) -> &Point2D<T> {
        &self.p2
    }

    /// The area contained by this rectangle.
    ///
    /// This is inclusive of the border.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Rectangle;
    ///
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 21);
    /// assert_eq!(rect.area(), 231);
    /// ```
    pub fn area(&self) -> T {
        self.width() * self.height()
    }

    /// The length of the side specified by the x-coordinates of the corners.
    ///
    /// This is inclusive of the border.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Rectangle;
    ///
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 21);
    /// assert_eq!(rect.width(), 11);
    /// ```
    pub fn width(&self) -> T {
        self.p2.x - self.p1.x + T::one()
    }

    /// The length of the side specified by the y-coordinates of the corners.
    ///
    /// This is inclusive of the border.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Rectangle;
    ///
    /// let rect = Rectangle::from_raw(10_i64, 1, 0, 21);
    /// assert_eq!(rect.height(), 21);
    /// ```
    pub fn height(&self) -> T {
        self.p2.y - self.p1.y + T::one()
    }
}

impl<T> From<(Point2D<T>, Point2D<T>)> for Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (Point2D<T>, Point2D<T>)) -> Self {
        Self::from_raw(value.0.x, value.0.y, value.1.x, value.1.y)
    }
}

impl<T> Display for Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Rectangle ({}, {}), ({}, {})",
            self.p1.x, self.p1.y, self.p2.x, self.p2.y
        )
    }
}

impl<T> Intersect for Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Intersection = Self;

    fn intersection(&self, other: &Self) -> Option<Self::Intersection> {
        let begin_x = self.p1.x.max(other.p1.x);
        let end_x = self.p2.x.min(other.p2.x);

        if begin_x > end_x {
            return None;
        }

        let begin_y = self.p1.y.max(other.p1.y);
        let end_y = self.p2.y.min(other.p2.y);

        if begin_y > end_y {
            return None;
        }

        Some(Self::from_raw(begin_x, begin_y, end_x, end_y))
    }

    fn intersects(&self, other: &Self) -> bool {
        let begin_x = self.p1.x.max(other.p1.x);
        let end_x = self.p2.x.min(other.p2.x);

        if begin_x > end_x {
            return false;
        }

        let begin_y = self.p1.y.max(other.p1.y);
        let end_y = self.p2.y.min(other.p2.y);

        begin_y <= end_y
    }
}

impl<T> Intersect<Point2D<T>> for Rectangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Intersection = Point2D<T>;

    fn intersection(&self, other: &Point2D<T>) -> Option<Self::Intersection> {
        if self.p1.x <= other.x
            && self.p2.x >= other.x
            && self.p1.y <= other.y
            && self.p2.y >= other.y
        {
            Some(*other)
        } else {
            None
        }
    }

    fn intersects(&self, other: &Point2D<T>) -> bool {
        self.p1.x <= other.x && self.p2.x >= other.x && self.p1.y <= other.y && self.p2.y >= other.y
    }
}
