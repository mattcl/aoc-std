use std::{fmt::Display, hash::Hash};

use num::{Bounded, Num};

use crate::{Intersect, Point3D, Rectangle};

/// A cube inclusively defined by two [Point3D] opposite corners.
///
/// The specified corners can be in any order as long as they are opposite.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cube<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub start: Point3D<T>,
    pub end: Point3D<T>,
}

impl<T> Cube<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Create a cube fromt he specified points.
    pub fn new(p1: Point3D<T>, p2: Point3D<T>) -> Self {
        let start = p1.min(p2);
        let end = p1.max(p2);

        Self { start, end }
    }

    /// The length of the cube in the x-axis, inclusive of the corners.
    pub fn width(&self) -> T {
        self.end.x - self.start.z + T::one()
    }

    /// The length of the cube in the y-axis, inclusive of the corners.
    pub fn height(&self) -> T {
        self.end.y - self.start.y + T::one()
    }

    /// The length of the cube in the z-axis, inclusive of the corners.
    pub fn depth(&self) -> T {
        self.end.z - self.start.z + T::one()
    }

    /// The volume enclosed by the cube (including the corners).
    pub fn volume(&self) -> T {
        self.width() * self.height() * self.depth()
    }

    /// The surface area of the cube made buy summing the areas of the faces.
    pub fn surface_area(&self) -> T {
        let xy = self.xy_face().area();
        let xz = self.xz_face().area();
        let yz = self.yz_face().area();

        xy + xy + xz + xz + yz + yz
    }

    /// Move `self` by treating `amounts` as a vector.
    pub fn translate(&mut self, amounts: Point3D<T>) {
        self.start += amounts;
        self.end += amounts;
    }

    /// Move `self` by `amount` along the x-axis.
    pub fn translate_x(&mut self, amount: T) {
        self.start.x = self.start.x + amount;
        self.end.x = self.end.x + amount;
    }

    /// Move `self` by `amount` along the y-axis.
    pub fn translate_y(&mut self, amount: T) {
        self.start.y = self.start.y + amount;
        self.end.y = self.end.y + amount;
    }

    /// Move `self` by `amount` along the z-axis.
    pub fn translate_z(&mut self, amount: T) {
        self.start.z = self.start.z + amount;
        self.end.z = self.end.z + amount;
    }

    /// Return a [Rectangle] representing the 2D projection of the cube onto the
    /// xy plane.
    pub fn xy_face(&self) -> Rectangle<T> {
        Rectangle::from_raw(self.start.x, self.start.y, self.end.x, self.end.y)
    }

    /// Return a [Rectangle] representing the 2D projection of the cube onto the
    /// xz plane.
    pub fn xz_face(&self) -> Rectangle<T> {
        Rectangle::from_raw(self.start.x, self.start.z, self.end.x, self.end.z)
    }

    /// Return a [Rectangle] representing the 2D projection of the cube onto the
    /// yz plane.
    pub fn yz_face(&self) -> Rectangle<T> {
        Rectangle::from_raw(self.start.y, self.start.z, self.end.y, self.end.z)
    }
}

impl<T> From<(Point3D<T>, Point3D<T>)> for Cube<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn from(value: (Point3D<T>, Point3D<T>)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl<T> Display for Cube<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Cube ({}, {}, {}), ({}, {}, {})",
            self.start.x, self.start.y, self.start.z, self.end.x, self.end.y, self.end.z
        )
    }
}

impl<T> Intersect<Point3D<T>> for Cube<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Intersection = Point3D<T>;

    fn intersection(&self, other: &Point3D<T>) -> Option<Self::Intersection> {
        if self.intersects(other) {
            Some(*other)
        } else {
            None
        }
    }

    fn intersects(&self, other: &Point3D<T>) -> bool {
        self.start.x <= other.x
            && other.x <= self.end.x
            && self.start.y <= other.y
            && other.y <= self.end.y
            && self.start.z <= other.z
            && other.z <= self.end.z
    }
}
