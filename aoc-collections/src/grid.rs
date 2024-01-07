use std::str::FromStr;

use aoc_directions::{BoundedCardinalNeighbors, Cardinal, Direction};
use aoc_geometry::Location;
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Error)]
pub enum GridError {
    #[error("Location {0:?} does not exist in the grid ")]
    OutOfBounds(Location),

    #[error("The grid does not have a consistent width")]
    InconsistentWidth,
}

/// A grid is a two-dimensional collection of `T`, optionally indexed by [Location].
///
/// Under the hood, it's a vector of `[rows][cols]`.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Grid<T> {
    pub locations: Vec<Vec<T>>,
    height: usize,
    width: usize,
}

impl<T> Grid<T> {
    /// Make a new grid from given data.
    pub fn new(locations: Vec<Vec<T>>) -> Self {
        let height = locations.len();
        let width = locations.first().map(|r| r.len()).unwrap_or_default();

        Self {
            locations,
            width,
            height,
        }
    }

    /// Returns `true` if every row in the grid is the same width.
    ///
    /// We don't check this as part of [Grid::new] for speed reasons, but it is
    /// useful in other instances.
    /// # Examples
    /// ```
    /// use aoc_collections::Grid;
    ///
    /// let g = Grid::new(vec![vec!['a'; 10]; 12]);
    /// assert!(g.consistent_width());
    ///
    /// let i = Grid::new(vec![
    ///     vec![0_i16; 10],
    ///     vec![0_i16; 11],
    /// ]);
    /// assert!(!i.consistent_width());
    /// ```
    pub fn consistent_width(&self) -> bool {
        self.locations.iter().all(|r| r.len() == self.width())
    }

    /// Attempt to get a reference to the value that corresponds to the given location.
    ///
    /// Returns [None] if the location does not exist in the grid.
    pub fn get(&self, location: &Location) -> Option<&T> {
        self.locations
            .get(location.row)
            .and_then(|r| r.get(location.col))
    }

    /// Attempt to get a mutable reference to the value for the given location.
    ///
    /// Returns [None] if the location does not exist in the grid.
    pub fn get_mut(&mut self, location: &Location) -> Option<&mut T> {
        self.locations
            .get_mut(location.row)
            .and_then(|r| r.get_mut(location.col))
    }

    /// Attempt to set the value in the grid corresponding to the given location.
    ///
    /// This will error if the location does not exist in the grid.
    pub fn set(&mut self, location: &Location, value: T) -> Result<(), GridError> {
        let e = self
            .get_mut(location)
            .ok_or(GridError::OutOfBounds(*location))?;
        *e = value;
        Ok(())
    }

    /// Get the width (number of columns) of this grid.
    pub fn width(&self) -> usize {
        self.width
    }

    /// Get the height (number of rows) of this grid.
    pub fn height(&self) -> usize {
        self.height
    }

    /// Get an iterator over the valid grid neighbors of the given location.
    ///
    /// This considers all eight neighboring locations.
    ///
    /// For convenience, this yields tuples of ([Direction], [Location], `&T`)
    pub fn neighbors(
        &self,
        location: &Location,
    ) -> impl Iterator<Item = (Direction, Location, &T)> {
        location
            .neighbors()
            .filter_map(|(dir, n)| self.get(&n).map(|v| (dir, n, v)))
    }

    /// Get an iterator over the valid grid cardinal neighbors of the given location.
    ///
    /// This considers all four cardinal neighboring locations.
    ///
    /// For convenience, this yields tuples of ([Cardinal], [Location], `&T`)
    pub fn cardinal_neighbors(
        &self,
        location: &Location,
    ) -> impl Iterator<Item = (Cardinal, Location, &T)> {
        location
            .cardinal_neighbors()
            .filter_map(|(dir, n)| self.get(&n).map(|v| (dir, n, v)))
    }

    /// Get the specified cardinal_neighbor and its value from the grid, if it
    /// exists.
    ///
    /// For convenience, this yields tuples of ([Cardinal], `&T`)
    pub fn cardinal_neighbor(
        &self,
        location: &Location,
        direction: Cardinal,
    ) -> Option<(Location, &T)> {
        location
            .cardinal_neighbor(direction)
            .and_then(|neighbor| self.get(&neighbor).map(|v| (neighbor, v)))
    }
}

impl<T: Default + Clone> Grid<T> {
    /// Construct an empty grid of type `T` with the given `width` and `height`.
    ///
    /// `T` must implement `Default` and `Clone`
    ///
    /// # Examples
    /// ```
    /// use aoc_collections::Grid;
    ///
    /// let g: Grid<u8> = Grid::default_with_dimensions(10, 15);
    /// assert_eq!(g.width(), 10);
    /// assert_eq!(g.height(), 15);
    /// ```
    pub fn default_with_dimensions(width: usize, height: usize) -> Self {
        vec![vec![T::default(); width]; height].into()
    }
}

impl<T> From<Vec<Vec<T>>> for Grid<T> {
    fn from(value: Vec<Vec<T>>) -> Self {
        Self::new(value)
    }
}

/// A [Grid] of single characters.
///
/// This may be constructed directly from a newline-delimited string, where
/// every non-newline char will be added to the grid.
///
/// # Examples
/// ```
/// use std::str::FromStr;
/// use aoc_collections::{Grid, CharGrid};
///
/// let input = "abc\ndef";
/// let g = CharGrid::from_str(input).unwrap();
/// let expected = Grid::new(vec![
///     vec!['a', 'b', 'c'],
///     vec!['d', 'e', 'f'],
/// ]);
///
/// assert_eq!(g, expected);
/// ```
pub type CharGrid = Grid<char>;

impl FromStr for CharGrid {
    type Err = GridError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let g = Self::new(
            s.trim()
                .lines()
                .map(|line| line.chars().collect::<Vec<_>>())
                .collect(),
        );

        if !g.consistent_width() {
            return Err(GridError::InconsistentWidth);
        }

        Ok(g)
    }
}

/// A [Grid] of single unsigned digits.
///
/// This may be constructed directly from a newline-delimited string, where
/// every non-newline char will be coverted to a `u8` and added to the grid.
///
/// # Examples
/// ```
/// use std::str::FromStr;
/// use aoc_collections::{Grid, DigitGrid};
///
/// let input = "012\n345";
/// let g = DigitGrid::from_str(input).unwrap();
/// let expected: Grid<u8> = Grid::new(vec![
///     vec![0, 1, 2],
///     vec![3, 4, 5],
/// ]);
///
/// assert_eq!(g, expected);
/// ```
pub type DigitGrid = Grid<u8>;

impl FromStr for DigitGrid {
    type Err = GridError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let g = Self::new(
            s.trim()
                .lines()
                .map(|line| {
                    line.chars()
                        .map(|ch| ch.to_digit(10).unwrap_or_default() as u8)
                        .collect::<Vec<_>>()
                })
                .collect(),
        );

        if !g.consistent_width() {
            return Err(GridError::InconsistentWidth);
        }

        Ok(g)
    }
}

#[cfg(test)]
mod tests {
    mod grid {
        use super::super::*;

        #[test]
        fn construction() {
            let d = vec![vec![false; 10]; 15];
            let g = Grid::from(d);
            assert_eq!(g.width(), 10);
            assert_eq!(g.height(), 15);
        }

        #[test]
        fn manipulation() {
            let d = vec![vec![false; 10]; 15];
            let mut g = Grid::from(d);
            let loc = Location::new(3, 4);
            assert_eq!(g.get(&loc), Some(&false));

            {
                let e = g.get_mut(&loc).unwrap();
                *e = true;
            }

            assert_eq!(g.get(&loc), Some(&true));

            g.set(&loc, false).unwrap();
            assert_eq!(g.get(&loc), Some(&false));

            // out of bounds
            let bad_loc = Location::new(14, 10);
            assert_eq!(g.set(&bad_loc, false), Err(GridError::OutOfBounds(bad_loc)));
        }
    }
}
