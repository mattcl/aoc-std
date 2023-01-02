use aoc_directions::{Cardinal, Direction};
use aoc_geometry::Location;
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Error)]
pub enum GridError {
    #[error("Location {0:?} does not exist in the grid ")]
    OutOfBounds(Location),
}

/// A grid a two-dimensional collection of `T`, optionally indexed by [Location].
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
        let width = locations.get(0).map(|r| r.len()).unwrap_or_default();

        Self {
            locations,
            width,
            height,
        }
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
            .ok_or_else(|| GridError::OutOfBounds(*location))?;
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
}

impl<T> From<Vec<Vec<T>>> for Grid<T> {
    fn from(value: Vec<Vec<T>>) -> Self {
        Self::new(value)
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
