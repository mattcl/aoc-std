use std::ops::Deref;

use num::{Bounded, Num};

/// A two-dimensional representaiton of a Pascal's Triangle of a given number
/// of rows.
///
/// # Examples
/// ```
/// use aoc_geometry::PascalsTriangle;
///
/// let t: PascalsTriangle<i64> = PascalsTriangle::new(4);
///
/// let expected = vec![
///     vec![1_i64],
///     vec![1, 1],
///     vec![1, 2, 1],
///     vec![1, 3, 3, 1],
/// ];
///
/// assert_eq!(*t, expected);
///
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PascalsTriangle<T>(Vec<Vec<T>>);

impl<T> Deref for PascalsTriangle<T> {
    type Target = Vec<Vec<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> PascalsTriangle<T>
where
    T: Num + Bounded + Ord + PartialOrd + Copy + Default,
{
    /// Generate a two-dimensional representaiton of Pascal's Triangle with `num_rows`.
    ///
    /// # Examples
    /// ```
    /// use aoc_geometry::PascalsTriangle;
    ///
    /// let t: PascalsTriangle<i64> = PascalsTriangle::new(4);
    ///
    /// let expected = vec![
    ///     vec![1_i64],
    ///     vec![1, 1],
    ///     vec![1, 2, 1],
    ///     vec![1, 3, 3, 1],
    /// ];
    ///
    /// assert_eq!(*t, expected);
    ///
    /// ```
    pub fn new(num_rows: usize) -> Self {
        let mut triangle = vec![vec![T::one()]];

        for i in 1..num_rows {
            let mut layer = Vec::with_capacity(i + 1);
            layer.push(T::one());
            layer.extend(
                triangle[i - 1]
                    .windows(2)
                    .map(|window| window[0] + window[1]),
            );
            layer.push(T::one());

            triangle.push(layer);
        }

        Self(triangle)
    }
}
