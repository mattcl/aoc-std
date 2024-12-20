//! Structs and traits for various points.
//!
//! Points can only contain signed values.
//!
//! For convenience, 2d and 3d points have specialized implementations that
//! expose specific attributes like x, y, z. Higher dimensional points are
//! available, but are generic via array wrappers.
use std::{
    cmp::Ordering,
    hash::Hash,
    iter::Sum,
    ops::{Add, AddAssign, Deref, DerefMut, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use aoc_directions::{
    BoundedCardinalNeighbors, BoundedOrdinalNeighbors, Cardinal, CardinalNeighbors, Direction,
    OrdinalNeighbors,
};
use num::{Bounded, Num, Signed};

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
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, PartialOrd, Ord, Hash)]
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

    /// Calculate the relative direction that `self` is from `other`.
    ///
    /// Returns [None] if `self == other`.
    pub fn relative_direction_from(&self, other: &Self) -> Option<Direction> {
        match (self.x.cmp(&other.x), self.y.cmp(&other.y)) {
            (Ordering::Less, Ordering::Less) => Some(Direction::SouthWest),
            (Ordering::Less, Ordering::Equal) => Some(Direction::West),
            (Ordering::Less, Ordering::Greater) => Some(Direction::NorthWest),
            (Ordering::Equal, Ordering::Less) => Some(Direction::South),
            (Ordering::Equal, Ordering::Equal) => None,
            (Ordering::Equal, Ordering::Greater) => Some(Direction::North),
            (Ordering::Greater, Ordering::Less) => Some(Direction::SouthEast),
            (Ordering::Greater, Ordering::Equal) => Some(Direction::East),
            (Ordering::Greater, Ordering::Greater) => Some(Direction::NorthEast),
        }
    }
}

impl<T> Point2D<T>
where
    T: Num + Bounded + Signed + Ord + PartialOrd + Copy + Default + Hash,
{
    /// Return the reflection of this point across the x-axis.
    ///
    /// This would be equal to a point with the sign of the `y` value flipped.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Point2D;
    ///
    /// let p = Point2D::new(2_i64, 3_i64);
    ///
    /// assert_eq!(p.reflect_x(), Point2D::new(2, -3));
    /// ```
    pub fn reflect_x(&self) -> Self {
        Self::new(self.x, -self.y)
    }

    /// Return the reflection of this point across the y-axis.
    ///
    /// This would be equal to a point with the sign of the `x` value flipped.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::Point2D;
    ///
    /// let p = Point2D::new(2_i64, 3_i64);
    ///
    /// assert_eq!(p.reflect_y(), Point2D::new(-2, 3));
    /// ```
    pub fn reflect_y(&self) -> Self {
        Self::new(-self.x, self.y)
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

impl<T> Add<Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<T> Add<&Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<T> Add<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl<T> Add<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x + rhs,
            y: self.y + rhs,
        }
    }
}

impl<T> Add<T> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn add(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x + rhs,
            y: self.y + rhs,
        }
    }
}

impl<T> AddAssign<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn add_assign(&mut self, rhs: Point2D<T>) {
        self.x = self.x + rhs.x;
        self.y = self.y + rhs.y;
    }
}

impl<T> AddAssign<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn add_assign(&mut self, rhs: &Point2D<T>) {
        self.x = self.x + rhs.x;
        self.y = self.y + rhs.y;
    }
}

impl<T> AddAssign<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn add_assign(&mut self, rhs: T) {
        self.x = self.x + rhs;
        self.y = self.y + rhs;
    }
}

impl<T> Sub<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<T> Sub<Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<T> Sub<&Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<T> Sub<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl<T> Sub<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x - rhs,
            y: self.y - rhs,
        }
    }
}

impl<T> Sub<T> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn sub(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x - rhs,
            y: self.y - rhs,
        }
    }
}

impl<T> SubAssign<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sub_assign(&mut self, rhs: Point2D<T>) {
        self.x = self.x - rhs.x;
        self.y = self.y - rhs.y;
    }
}

impl<T> SubAssign<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sub_assign(&mut self, rhs: &Point2D<T>) {
        self.x = self.x - rhs.x;
        self.y = self.y - rhs.y;
    }
}

impl<T> SubAssign<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sub_assign(&mut self, rhs: T) {
        self.x = self.x - rhs;
        self.y = self.y - rhs;
    }
}

impl<T> Mul<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Self;

    fn mul(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x * rhs.x,
            y: self.y * rhs.y,
        }
    }
}

impl<T> Mul<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Self;

    fn mul(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x * rhs.x,
            y: self.y * rhs.y,
        }
    }
}

impl<T> Mul<&Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn mul(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x * rhs.x,
            y: self.y * rhs.y,
        }
    }
}

impl<T> Mul<Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn mul(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x * rhs.x,
            y: self.y * rhs.y,
        }
    }
}

impl<T> Mul<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn mul(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

impl<T> Mul<T> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn mul(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

impl<T> MulAssign<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn mul_assign(&mut self, rhs: Point2D<T>) {
        self.x = self.x * rhs.x;
        self.y = self.y * rhs.y;
    }
}

impl<T> MulAssign<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn mul_assign(&mut self, rhs: &Point2D<T>) {
        self.x = self.x * rhs.x;
        self.y = self.y * rhs.y;
    }
}

impl<T> MulAssign<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn mul_assign(&mut self, rhs: T) {
        self.x = self.x * rhs;
        self.y = self.y * rhs;
    }
}

impl<T> Div<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Self;

    fn div(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x / rhs.x,
            y: self.y / rhs.y,
        }
    }
}

impl<T> Div<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Self;

    fn div(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x / rhs.x,
            y: self.y / rhs.y,
        }
    }
}

impl<T> Div<&Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn div(self, rhs: &Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x / rhs.x,
            y: self.y / rhs.y,
        }
    }
}

impl<T> Div<Point2D<T>> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn div(self, rhs: Point2D<T>) -> Self::Output {
        Self::Output {
            x: self.x / rhs.x,
            y: self.y / rhs.y,
        }
    }
}

impl<T> Div<T> for &Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn div(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x / rhs,
            y: self.y / rhs,
        }
    }
}

impl<T> Div<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point2D<T>;

    fn div(self, rhs: T) -> Self::Output {
        Self::Output {
            x: self.x / rhs,
            y: self.y / rhs,
        }
    }
}

impl<T> DivAssign<Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn div_assign(&mut self, rhs: Point2D<T>) {
        self.x = self.x / rhs.x;
        self.y = self.y / rhs.y;
    }
}

impl<T> DivAssign<&Point2D<T>> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn div_assign(&mut self, rhs: &Point2D<T>) {
        self.x = self.x / rhs.x;
        self.y = self.y / rhs.y;
    }
}

impl<T> DivAssign<T> for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn div_assign(&mut self, rhs: T) {
        self.x = self.x / rhs;
        self.y = self.y / rhs;
    }
}

impl<T> Sum for Point2D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(Self::add).unwrap_or_default()
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

/// Implement CardinalNeighbors for the specified types
macro_rules! impl_cardinal {
    ($($x:ty),+ $(,)?) => {
        $(
            impl CardinalNeighbors for Point2D<$x> {
                fn north(&self) -> Self {
                    (self.x, self.y + 1).into()
                }

                fn south(&self) -> Self {
                    (self.x, self.y - 1).into()
                }

                fn east(&self) -> Self {
                    (self.x + 1, self.y).into()
                }

                fn west(&self) -> Self {
                    (self.x - 1, self.y).into()
                }
            }
        )*
    };
}

/// Implement BoundedCardinalNeighbors for the specified types
macro_rules! impl_bounded_cardinal {
    ($($x:ty),+ $(,)?) => {
        $(
            impl BoundedCardinalNeighbors for Point2D<$x> {
                fn north(&self) -> Option<Self> {
                    Some((self.x, self.y + 1).into())
                }

                fn south(&self) -> Option<Self> {
                    if self.y == 0 {
                        None
                    } else {
                        Some((self.x, self.y - 1).into())
                    }
                }

                fn east(&self) -> Option<Self> {
                    Some((self.x + 1, self.y).into())
                }

                fn west(&self) -> Option<Self> {
                    if self.x == 0 {
                        None
                    } else {
                        Some((self.x - 1, self.y).into())
                    }
                }
            }
        )*
    };
}

/// Implement OrdinalNeighbors for the specified types
macro_rules! impl_ordinal {
    ($($x:ty),+ $(,)?) => {
        $(
            impl OrdinalNeighbors for Point2D<$x> {
                fn north_east(&self) -> Self {
                    (self.x + 1, self.y + 1).into()
                }

                fn north_west(&self) -> Self {
                    (self.x - 1, self.y + 1).into()
                }

                fn south_east(&self) -> Self {
                    (self.x + 1, self.y - 1).into()
                }

                fn south_west(&self) -> Self {
                    (self.x - 1, self.y - 1).into()
                }
            }
        )*
    };
}

/// Implement BoundedOrdinalNeighbors for the specified types
macro_rules! impl_bounded_ordinal {
    ($($x:ty),+ $(,)?) => {
        $(
            impl BoundedOrdinalNeighbors for Point2D<$x> {
                fn north_east(&self) -> Option<Self> {
                    Some((self.x + 1, self.y + 1).into())
                }

                fn north_west(&self) -> Option<Self> {
                    if self.x == 0 {
                        None
                    } else {
                        Some((self.x - 1, self.y + 1).into())
                    }
                }

                fn south_east(&self) -> Option<Self> {
                    if self.y == 0 {
                        None
                    } else {
                        Some((self.x + 1, self.y - 1).into())
                    }
                }

                fn south_west(&self) -> Option<Self> {
                    if self.x == 0 || self.y == 0 {
                        None
                    } else {
                        Some((self.x - 1, self.y - 1).into())
                    }
                }
            }
        )*
    };
}

macro_rules! impl_neighbors_iter {
    ($($x:ty),+ $(,)?) => {
        $(
            impl Point2D<$x> {
                const CARD_NEIGHBOR_OFFSETS: [(Cardinal, $x, $x); 4] = [
                    (Cardinal::North, 0, 1),
                    (Cardinal::East, 1, 0),
                    (Cardinal::South, 0, -1),
                    (Cardinal::West, -1, 0),
                ];

                const NEIGHBOR_OFFSETS: [(Direction, $x, $x); 8] = [
                    (Direction::North, 0, 1),
                    (Direction::NorthEast, 1, 1),
                    (Direction::East, 1, 0),
                    (Direction::SouthEast, 1, -1),
                    (Direction::South, 0, -1),
                    (Direction::SouthWest, -1, -1),
                    (Direction::West, -1, 0),
                    (Direction::NorthWest, -1, 1),
                ];

                /// Returns an iterator over the valid cardinal neighbors of this point.
                ///
                /// Order is N -> E -> S -> W
                pub fn cardinal_neighbors(&self) -> impl Iterator<Item = (Cardinal, Self)> {
                    let x = self.x;
                    let y = self.y;
                    Self::CARD_NEIGHBOR_OFFSETS
                        .iter()
                        .map(move |(dir, dx, dy)| (*dir, Self::new(x + dx, y + dy)))
                }

                /// Returns an iterator over the valid cardinal and ordinal neighbors.
                ///
                /// Order is N -> NE -> E -> SE -> S -> SW -> W -> NW
                pub fn neighbors(&self) -> impl Iterator<Item = (Direction, Self)> {
                    let x = self.x;
                    let y = self.y;
                    Self::NEIGHBOR_OFFSETS
                        .iter()
                        .map(move |(dir, dx, dy)| (*dir, Self::new(x + dx, y + dy)))
                }
            }
        )*
    };
}

macro_rules! impl_bounded_neighbors_iter {
    ($(($x:ty, $y:ty)),+ $(,)?) => {
        $(
            impl Point2D<$x> {
                const CARD_NEIGHBOR_OFFSETS: [(Cardinal, $y, $y); 4] = [
                    (Cardinal::North, 0, 1),
                    (Cardinal::East, 1, 0),
                    (Cardinal::South, 0, -1),
                    (Cardinal::West, -1, 0),
                ];

                const NEIGHBOR_OFFSETS: [(Direction, $y, $y); 8] = [
                    (Direction::North, 0, 1),
                    (Direction::NorthEast, 1, 1),
                    (Direction::East, 1, 0),
                    (Direction::SouthEast, 1, -1),
                    (Direction::South, 0, -1),
                    (Direction::SouthWest, -1, -1),
                    (Direction::West, -1, 0),
                    (Direction::NorthWest, -1, 1),
                ];

                /// Returns an iterator over the valid cardinal neighbors of this point.
                ///
                /// Order is N -> E -> S -> W
                pub fn cardinal_neighbors(&self) -> impl Iterator<Item = (Cardinal, Self)> {
                    let x = self.x;
                    let y = self.y;

                    Self::CARD_NEIGHBOR_OFFSETS
                        .iter()
                        .filter_map(move |(dir, dx, dy)| {
                            if x == 0 && *dx < 0 {
                                return None;
                            }

                            if y == 0 && *dy < 0 {
                                return None;
                            }

                            Some((
                                *dir,
                                Self::new(
                                    (x as $y + dx) as $x,
                                    (y as $y + dy) as $x,
                                )
                            ))
                        })
                }

                /// Returns an iterator over the valid cardinal and ordinal neighbors.
                ///
                /// Order is N -> NE -> E -> SE -> S -> SW -> W -> NW
                pub fn neighbors(&self) -> impl Iterator<Item = (Direction, Self)> {
                    let x = self.x;
                    let y = self.y;

                    Self::NEIGHBOR_OFFSETS
                        .iter()
                        .filter_map(move |(dir, dx, dy)| {
                            if x == 0 && *dx < 0 {
                                return None;
                            }

                            if y == 0 && *dy < 0 {
                                return None;
                            }

                            Some((
                                *dir,
                                Self::new(
                                    (x as $y + dx) as $x,
                                    (y as $y + dy) as $x,
                                )
                            ))
                        })
                }
            }
        )*
    };
}

macro_rules! impl_project {
    ($($x:ty),+ $(,)?) => {
        $(
            impl Point2D<$x> {
                /// Projects self along `dir` by `distance`.
                ///
                /// `distance` can be thought of as the number of steps, so in
                /// the case of the ordinal directions, the actual distance from
                /// the new point to self would be longer because it's a
                /// diagonal, but the number of "steps" shifted is the same.
                pub fn project(&self, dir: &Direction, distance: $x) -> Self {
                    match dir {
                        Direction::North => Self::new(self.x, self.y + distance),
                        Direction::NorthEast => Self::new(self.x + distance, self.y + distance),
                        Direction::East => Self::new(self.x + distance, self.y),
                        Direction::SouthEast => Self::new(self.x + distance, self.y - distance),
                        Direction::South => Self::new(self.x, self.y - distance),
                        Direction::SouthWest => Self::new(self.x - distance, self.y - distance),
                        Direction::West => Self::new(self.x - distance, self.y),
                        Direction::NorthWest => Self::new(self.x - distance, self.y + distance),
                    }
                }
            }
        )*
    };
}

macro_rules! impl_bounded_project {
    ($($x:ty),+ $(,)?) => {
        $(
            impl Point2D<$x> {
                /// Projects self along `dir` by `distance`.
                ///
                /// `distance` can be thought of as the number of steps, so in
                /// the case of the ordinal directions, the actual distance from
                /// the new point to self would be longer because it's a
                /// diagonal, but the number of "steps" shifted is the same.
                pub fn project(&self, dir: &Direction, distance: $x) -> Option<Self> {
                    match dir {
                        Direction::North => Some(Self::new(self.x, self.y + distance)),
                        Direction::NorthEast => Some(Self::new(self.x + distance, self.y + distance)),
                        Direction::East => Some(Self::new(self.x + distance, self.y)),
                        Direction::SouthEast => {
                            if self.y >= distance {
                                Some(Self::new(self.x + distance, self.y - distance))
                            } else {
                                None
                            }
                        },
                        Direction::South => {
                            if self.y >= distance {
                                Some(Self::new(self.x, self.y - distance))
                            } else {
                                None
                            }
                        },
                        Direction::SouthWest => {
                            if self.x >= distance && self.y >= distance {
                                Some(Self::new(self.x - distance, self.y - distance))
                            } else {
                                None
                            }
                        },
                        Direction::West => {
                            if self.x >= distance {
                                Some(Self::new(self.x - distance, self.y))
                            } else {
                                None
                            }
                        },
                        Direction::NorthWest => {
                            if self.x >= distance {
                                Some(Self::new(self.x - distance, self.y + distance))
                            } else {
                                None
                            }
                        }
                    }
                }
            }
        )*
    };
}

// we handle these specifically instead of trying to use some type constraint
// magic to have generic impls for the ones we want. Part of the limitation
// for the neighbors iterators is not being able to specify the `impl Iterator`
// in the trait.
impl_cardinal!(i8, i16, i32, i64, i128, isize);
impl_neighbors_iter!(i8, i16, i32, i64, i128, isize);
impl_bounded_cardinal!(u8, u16, u32, u64, u128, usize);
impl_ordinal!(i8, i16, i32, i64, i128, isize);
impl_bounded_ordinal!(u8, u16, u32, u64, u128, usize);
impl_bounded_neighbors_iter! {
    (u8, i16),
    (u16, i16),
    (u32, i32),
    (u64, i64),
    (u128, i128),
    (usize, isize),
}
impl_project!(i8, i16, i32, i64, i128, isize);
impl_bounded_project!(u8, u16, u32, u64, u128, usize);

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
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, PartialOrd, Ord, Hash)]
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

impl<T> Add<Point3D<T>> for &Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn add(self, rhs: Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl<T> Add<&Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn add(self, rhs: &Point3D<T>) -> Self::Output {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl<T> Add<&Point3D<T>> for &Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn add(self, rhs: &Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl<T> AddAssign<Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn add_assign(&mut self, rhs: Point3D<T>) {
        self.x = self.x + rhs.x;
        self.y = self.y + rhs.y;
        self.z = self.z + rhs.z;
    }
}

impl<T> AddAssign<&Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn add_assign(&mut self, rhs: &Point3D<T>) {
        self.x = self.x + rhs.x;
        self.y = self.y + rhs.y;
        self.z = self.z + rhs.z;
    }
}

impl<T> Sub<Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn sub(self, rhs: Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl<T> Sub<Point3D<T>> for &Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn sub(self, rhs: Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl<T> Sub<&Point3D<T>> for &Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn sub(self, rhs: &Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl<T> Sub<&Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = Point3D<T>;

    fn sub(self, rhs: &Point3D<T>) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl<T> SubAssign<Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sub_assign(&mut self, rhs: Point3D<T>) {
        self.x = self.x - rhs.x;
        self.y = self.y - rhs.y;
        self.z = self.z - rhs.z;
    }
}

impl<T> SubAssign<&Point3D<T>> for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sub_assign(&mut self, rhs: &Point3D<T>) {
        self.x = self.x - rhs.x;
        self.y = self.y - rhs.y;
        self.z = self.z - rhs.z;
    }
}

impl<T> Sum for Point3D<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(Self::add).unwrap_or_default()
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
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
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

impl<const N: usize, T> DerefMut for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
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

impl<const N: usize, T> Add<PointND<N, T>> for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = PointND<N, T>;

    fn add(self, rhs: PointND<N, T>) -> Self::Output {
        let mut out = Self::default();
        for i in 0..N {
            out.0[i] = self.0[i] + rhs.0[i];
        }
        out
    }
}

impl<const N: usize, T> Sub<PointND<N, T>> for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    type Output = PointND<N, T>;

    fn sub(self, rhs: PointND<N, T>) -> Self::Output {
        let mut out = Self::default();
        for i in 0..N {
            out.0[i] = self.0[i] - rhs.0[i];
        }
        out
    }
}

impl<const N: usize, T> Sum for PointND<N, T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(Self::add).unwrap_or_default()
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

const LOC_CARD_NEIGHBOR_OFFSETS: [(Cardinal, i64, i64); 4] = [
    (Cardinal::North, -1, 0),
    (Cardinal::East, 0, 1),
    (Cardinal::South, 1, 0),
    (Cardinal::West, 0, -1),
];

const LOC_NEIGHBOR_OFFSETS: [(Direction, i64, i64); 8] = [
    (Direction::North, -1, 0),
    (Direction::NorthEast, -1, 1),
    (Direction::East, 0, 1),
    (Direction::SouthEast, 1, 1),
    (Direction::South, 1, 0),
    (Direction::SouthWest, 1, -1),
    (Direction::West, 0, -1),
    (Direction::NorthWest, -1, -1),
];

/// Locations are special (row, colum) points mainly used as indexes into grids.
///
/// Locations also differ in that "north" is decreasing row values and "south"
/// is increasing row values.
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub row: usize,
    pub col: usize,
}

impl Location {
    pub fn new(row: usize, col: usize) -> Self {
        Self { row, col }
    }

    /// Returns an iterator over the valid cardinal neighbors of this location.
    ///
    /// Order is N -> E -> S -> W
    pub fn cardinal_neighbors(&self) -> impl Iterator<Item = (Cardinal, Self)> {
        let row = self.row;
        let col = self.col;

        LOC_CARD_NEIGHBOR_OFFSETS
            .iter()
            .filter_map(move |(dir, dr, dc)| {
                if *dr < 0 && row == 0 {
                    return None;
                }

                if *dc < 0 && col == 0 {
                    return None;
                }

                Some((
                    *dir,
                    ((row as i64 + *dr) as usize, (col as i64 + *dc) as usize).into(),
                ))
            })
    }

    /// Returns an iterator over the valid cardinal and ordinal neighbors.
    ///
    /// Order is N -> NE -> E -> SE -> S -> SW -> W -> NW
    pub fn neighbors(&self) -> impl Iterator<Item = (Direction, Self)> {
        let row = self.row;
        let col = self.col;

        LOC_NEIGHBOR_OFFSETS
            .iter()
            .filter_map(move |(dir, dr, dc)| {
                if *dr < 0 && row == 0 {
                    return None;
                }

                if *dc < 0 && col == 0 {
                    return None;
                }

                Some((
                    *dir,
                    ((row as i64 + *dr) as usize, (col as i64 + *dc) as usize).into(),
                ))
            })
    }

    /// Returns the immediate neighbor in the specified direction, if it exists.
    pub fn neighbor(&self, direction: Direction) -> Option<Self> {
        self.project(&direction, 1)
    }

    /// Calculate the relative direction that `self` is from `other`.
    ///
    /// Returns [None] if `self == other`.
    pub fn relative_direction_from(&self, other: &Self) -> Option<Direction> {
        match (self.col.cmp(&other.col), self.row.cmp(&other.row)) {
            (Ordering::Less, Ordering::Less) => Some(Direction::NorthWest),
            (Ordering::Less, Ordering::Equal) => Some(Direction::West),
            (Ordering::Less, Ordering::Greater) => Some(Direction::SouthWest),
            (Ordering::Equal, Ordering::Less) => Some(Direction::North),
            (Ordering::Equal, Ordering::Equal) => None,
            (Ordering::Equal, Ordering::Greater) => Some(Direction::South),
            (Ordering::Greater, Ordering::Less) => Some(Direction::NorthEast),
            (Ordering::Greater, Ordering::Equal) => Some(Direction::East),
            (Ordering::Greater, Ordering::Greater) => Some(Direction::SouthEast),
        }
    }

    /// Projects self along `dir` by `distance`.
    ///
    /// `distance` can be thought of as the number of steps, so in
    /// the case of the ordinal directions, the actual distance from
    /// the new point to self would be longer because it's a
    /// diagonal, but the number of "steps" shifted is the same.
    pub fn project(&self, dir: &Direction, distance: usize) -> Option<Self> {
        match dir {
            Direction::North => {
                if self.row >= distance {
                    Some(Self::new(self.row - distance, self.col))
                } else {
                    None
                }
            }
            Direction::NorthEast => {
                if self.row >= distance {
                    Some(Self::new(self.row - distance, self.col + distance))
                } else {
                    None
                }
            }
            Direction::East => Some(Self::new(self.row, self.col + distance)),
            Direction::SouthEast => Some(Self::new(self.row + distance, self.col + distance)),
            Direction::South => Some(Self::new(self.row + distance, self.col)),
            Direction::SouthWest => {
                if self.col >= distance {
                    Some(Self::new(self.row + distance, self.col - distance))
                } else {
                    None
                }
            }
            Direction::West => {
                if self.col >= distance {
                    Some(Self::new(self.row, self.col - distance))
                } else {
                    None
                }
            }
            Direction::NorthWest => {
                if self.row >= distance && self.col >= distance {
                    Some(Self::new(self.row - distance, self.col - distance))
                } else {
                    None
                }
            }
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

impl BoundedCardinalNeighbors for Location {
    fn north(&self) -> Option<Self> {
        if self.row == 0 {
            None
        } else {
            Some((self.row - 1, self.col).into())
        }
    }

    fn south(&self) -> Option<Self> {
        Some((self.row + 1, self.col).into())
    }

    fn east(&self) -> Option<Self> {
        Some((self.row, self.col + 1).into())
    }

    fn west(&self) -> Option<Self> {
        if self.col == 0 {
            None
        } else {
            Some((self.row, self.col - 1).into())
        }
    }
}

impl BoundedOrdinalNeighbors for Location {
    fn north_east(&self) -> Option<Self> {
        if self.row == 0 {
            None
        } else {
            Some((self.row - 1, self.col + 1).into())
        }
    }

    fn north_west(&self) -> Option<Self> {
        if self.row == 0 || self.col == 0 {
            None
        } else {
            Some((self.row - 1, self.col - 1).into())
        }
    }

    fn south_east(&self) -> Option<Self> {
        Some((self.row + 1, self.col + 1).into())
    }

    fn south_west(&self) -> Option<Self> {
        if self.col == 0 {
            None
        } else {
            Some((self.row + 1, self.col - 1).into())
        }
    }
}

#[cfg(test)]
mod tests {
    #[allow(non_snake_case)]
    mod Point2D {
        use super::super::*;

        // make it esay to test all of our intentionally supported types
        macro_rules! test_neighbors {
            ($(($n:ident, $x:ty)),+ $(,)?) => {
                $(
                    mod $n {
                        use super::super::super::*;

                        #[test]
                        fn north() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north(), Point2D::new(0, 1));
                        }

                        #[test]
                        fn south() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south(), Point2D::new(0, -1));
                        }

                        #[test]
                        fn east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.east(), Point2D::new(1, 0));
                        }

                        #[test]
                        fn west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.west(), Point2D::new(-1, 0));
                        }

                        #[test]
                        fn north_east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north_east(), Point2D::new(1, 1));
                        }

                        #[test]
                        fn north_west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north_west(), Point2D::new(-1, 1));
                        }

                        #[test]
                        fn south_east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south_east(), Point2D::new(1, -1));
                        }

                        #[test]
                        fn south_west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south_west(), Point2D::new(-1, -1));
                        }

                        #[test]
                        fn cardinal_neighbors() {
                            let p: Point2D<$x> = Point2D::default();
                            let expected = vec![
                                (Cardinal::North, p.north()),
                                (Cardinal::East, p.east()),
                                (Cardinal::South, p.south()),
                                (Cardinal::West, p.west()),
                            ];

                            let n = p.cardinal_neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);
                        }

                        #[test]
                        fn cardinal_neighbor() {
                            let p: Point2D<$x> = Point2D::default();

                            assert_eq!(p.cardinal_neighbor(Cardinal::North), p.north());
                            assert_eq!(p.cardinal_neighbor(Cardinal::East), p.east());
                            assert_eq!(p.cardinal_neighbor(Cardinal::South), p.south());
                            assert_eq!(p.cardinal_neighbor(Cardinal::West), p.west());
                        }

                        #[test]
                        fn neighbors() {
                            let p: Point2D<$x> = Point2D::default();
                            let expected = vec![
                                (Direction::North, p.north()),
                                (Direction::NorthEast, p.north_east()),
                                (Direction::East, p.east()),
                                (Direction::SouthEast, p.south_east()),
                                (Direction::South, p.south()),
                                (Direction::SouthWest, p.south_west()),
                                (Direction::West, p.west()),
                                (Direction::NorthWest, p.north_west()),
                            ];

                            let n = p.neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);
                        }
                    }
                )*
            };
        }

        // make it esay to test all of our intentionally supported types
        macro_rules! test_bounded_neighbors {
            ($(($n:ident, $x:ty)),+ $(,)?) => {
                $(
                    mod $n {
                        use super::super::super::*;

                        #[test]
                        fn north() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north(), Some(Point2D::new(0, 1)));
                        }

                        #[test]
                        fn south() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south(), None);


                            let p: Point2D<$x> = (2, 2).into();
                            assert_eq!(p.south(), Some((2, 1).into()));
                        }

                        #[test]
                        fn east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.east(), Some(Point2D::new(1, 0)));
                        }

                        #[test]
                        fn west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.west(), None);

                            let p: Point2D<$x> = (2, 2).into();
                            assert_eq!(p.west(), Some((1, 2).into()));
                        }

                        #[test]
                        fn north_east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north_east(), Some(Point2D::new(1, 1)));
                        }

                        #[test]
                        fn north_west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.north_west(), None);

                            let p: Point2D<$x> = (2, 2).into();
                            assert_eq!(p.north_west(), Some((1, 3).into()));
                        }

                        #[test]
                        fn south_east() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south_east(), None);

                            let p: Point2D<$x> = (2, 2).into();
                            assert_eq!(p.south_east(), Some((3, 1).into()));
                        }

                        #[test]
                        fn south_west() {
                            let p: Point2D<$x> = Point2D::default();
                            assert_eq!(p.south_west(), None);

                            let p: Point2D<$x> = (2, 2).into();
                            assert_eq!(p.south_west(), Some((1, 1).into()));
                        }

                        #[test]
                        fn cardinal_neighbors() {
                            let p: Point2D<$x> = Point2D::new(0, 0);
                            let expected = vec![
                                (Cardinal::North, p.north().unwrap()),
                                (Cardinal::East, p.east().unwrap()),
                            ];

                            let n = p.cardinal_neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);

                            let p: Point2D<$x> = Point2D::new(1, 1);
                            let expected = vec![
                                (Cardinal::North, p.north().unwrap()),
                                (Cardinal::East, p.east().unwrap()),
                                (Cardinal::South, p.south().unwrap()),
                                (Cardinal::West, p.west().unwrap()),
                            ];

                            let n = p.cardinal_neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);
                        }

                        #[test]
                        fn cardinal_neighbor() {
                            let p: Point2D<$x> = Point2D::new(1, 1);

                            assert_eq!(p.cardinal_neighbor(Cardinal::North), p.north());
                            assert_eq!(p.cardinal_neighbor(Cardinal::East), p.east());
                            assert_eq!(p.cardinal_neighbor(Cardinal::South), p.south());
                            assert_eq!(p.cardinal_neighbor(Cardinal::West), p.west());
                        }

                        #[test]
                        fn neighbors() {
                            let p: Point2D<$x> = Point2D::new(0, 0);
                            let expected = vec![
                                (Direction::North, p.north().unwrap()),
                                (Direction::NorthEast, p.north_east().unwrap()),
                                (Direction::East, p.east().unwrap()),
                            ];

                            let n = p.neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);

                            let p: Point2D<$x> = Point2D::new(1, 1);
                            let expected = vec![
                                (Direction::North, p.north().unwrap()),
                                (Direction::NorthEast, p.north_east().unwrap()),
                                (Direction::East, p.east().unwrap()),
                                (Direction::SouthEast, p.south_east().unwrap()),
                                (Direction::South, p.south().unwrap()),
                                (Direction::SouthWest, p.south_west().unwrap()),
                                (Direction::West, p.west().unwrap()),
                                (Direction::NorthWest, p.north_west().unwrap()),
                            ];

                            let n = p.neighbors().collect::<Vec<_>>();
                            assert_eq!(n, expected);
                        }
                    }
                )*
            };
        }

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
        fn summation() {
            let v = vec![
                Point2D::new(2_i64, 3),
                Point2D::new(-1_i64, 15),
                Point2D::new(12_i64, 11),
                Point2D::new(71_i64, 2),
                Point2D::new(5_i64, 0),
            ];

            let expected = Point2D::new(89_i64, 31);

            assert_eq!(v.into_iter().sum::<Point2D<i64>>(), expected);
        }

        test_neighbors! {
            (i8, i8),
            (i16, i16),
            (i32, i32),
            (i64, i64),
            (i128, i128),
            (isize, isize),
        }

        test_bounded_neighbors! {
            (u8, u8),
            (u16, u16),
            (u32, u32),
            (u64, u64),
            (u128, u128),
            (usize, usize),
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
            assert_eq!(p.north(), None);

            let p = Location::new(2, 2);
            assert_eq!(p.north(), Some((1, 2).into()));
        }

        #[test]
        fn south() {
            let p = Location::default();
            assert_eq!(p.south(), Some((1, 0).into()));
        }

        #[test]
        fn east() {
            let p = Location::default();
            assert_eq!(p.east(), Some(Location::new(0, 1)));
        }

        #[test]
        fn west() {
            let p = Location::default();
            assert_eq!(p.west(), None);

            let p = Location::new(2, 2);
            assert_eq!(p.west(), Some((2, 1).into()));
        }

        #[test]
        fn north_east() {
            let p = Location::default();
            assert_eq!(p.north_east(), None);

            let p = Location::new(2, 2);
            assert_eq!(p.north_east(), Some(Location::new(1, 3)));
        }

        #[test]
        fn north_west() {
            let p = Location::default();
            assert_eq!(p.north_west(), None);

            let p = Location::new(2, 2);
            assert_eq!(p.north_west(), Some((1, 1).into()));
        }

        #[test]
        fn south_east() {
            let p = Location::default();
            assert_eq!(p.south_east(), Some((1, 1).into()));
        }

        #[test]
        fn south_west() {
            let p = Location::default();
            assert_eq!(p.south_west(), None);

            let p = Location::new(2, 2);
            assert_eq!(p.south_west(), Some((3, 1).into()));
        }

        #[test]
        fn cardinal_neighbors() {
            let p = Location::new(2, 2);
            let expected = vec![
                (Cardinal::North, p.north().unwrap()),
                (Cardinal::East, p.east().unwrap()),
                (Cardinal::South, p.south().unwrap()),
                (Cardinal::West, p.west().unwrap()),
            ];

            let n = p.cardinal_neighbors().collect::<Vec<_>>();
            assert_eq!(n, expected);
        }

        #[test]
        fn cardinal_neighbor() {
            let p = Location::new(1, 1);

            assert_eq!(p.cardinal_neighbor(Cardinal::North), p.north());
            assert_eq!(p.cardinal_neighbor(Cardinal::East), p.east());
            assert_eq!(p.cardinal_neighbor(Cardinal::South), p.south());
            assert_eq!(p.cardinal_neighbor(Cardinal::West), p.west());
        }

        #[test]
        fn neighbors() {
            let p = Location::new(2, 2);
            let expected = vec![
                (Direction::North, p.north().unwrap()),
                (Direction::NorthEast, p.north_east().unwrap()),
                (Direction::East, p.east().unwrap()),
                (Direction::SouthEast, p.south_east().unwrap()),
                (Direction::South, p.south().unwrap()),
                (Direction::SouthWest, p.south_west().unwrap()),
                (Direction::West, p.west().unwrap()),
                (Direction::NorthWest, p.north_west().unwrap()),
            ];

            let n = p.neighbors().collect::<Vec<_>>();
            assert_eq!(n, expected);
        }

        #[test]
        fn relative_direction_from() {
            let p = Location::new(1, 1);
            assert_eq!(p.relative_direction_from(&p), None);
            assert_eq!(
                p.relative_direction_from(&Location::new(0, 0)),
                Some(Direction::SouthEast)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(0, 1)),
                Some(Direction::South)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(0, 2)),
                Some(Direction::SouthWest)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(1, 0)),
                Some(Direction::East)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(1, 2)),
                Some(Direction::West)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(2, 0)),
                Some(Direction::NorthEast)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(2, 1)),
                Some(Direction::North)
            );
            assert_eq!(
                p.relative_direction_from(&Location::new(2, 2)),
                Some(Direction::NorthWest)
            );
        }

        #[test]
        fn projecting() {
            let p = Location::new(2, 2);
            assert_eq!(p.project(&Direction::North, 2), Some(Location::new(0, 2)));
            assert_eq!(p.project(&Direction::North, 3), None,);
            assert_eq!(
                p.project(&Direction::NorthEast, 2),
                Some(Location::new(0, 4))
            );
            assert_eq!(p.project(&Direction::NorthEast, 3), None,);
            assert_eq!(p.project(&Direction::East, 2), Some(Location::new(2, 4)));
            assert_eq!(
                p.project(&Direction::SouthEast, 2),
                Some(Location::new(4, 4))
            );
            assert_eq!(p.project(&Direction::South, 2), Some(Location::new(4, 2)));
            assert_eq!(
                p.project(&Direction::SouthWest, 2),
                Some(Location::new(4, 0))
            );
            assert_eq!(p.project(&Direction::SouthWest, 3), None,);
            assert_eq!(p.project(&Direction::West, 2), Some(Location::new(2, 0)));
            assert_eq!(p.project(&Direction::West, 3), None,);
            assert_eq!(
                p.project(&Direction::NorthWest, 2),
                Some(Location::new(0, 0))
            );
            assert_eq!(p.project(&Direction::NorthWest, 3), None,);
        }
    }
}
