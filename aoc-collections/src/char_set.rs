use std::{
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign},
    str::FromStr,
};

use aoc_conversions::chars::num_to_ascii_alpha;
use aoc_types::{chars::AlphaError, Alpha, LowerAlpha, UpperAlpha};
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub enum CharSetError {
    #[error(transparent)]
    AlphaError(#[from] AlphaError),
}

/// A HashSet-like collection for ascii alpha characters backed by a single u64.
///
/// # Examples
/// ```
/// # use std::str::FromStr;
/// # use aoc_types::Alpha;
/// # use aoc_collections::CharSet;
///
/// let mut s = CharSet::from_str("hello").unwrap();
///
/// assert_eq!(s.len(), 4);
/// assert!(s.contains(Alpha::try_from('e').unwrap()));
///
/// let w = Alpha::try_from('W').unwrap();
/// s.insert(w);
///
/// assert!(s.contains(w));
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharSet(u64);

impl CharSet {
    /// Returns the number of elements in the set.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use aoc_collections::CharSet;
    /// let s = CharSet::from_str("hello").unwrap();
    ///
    /// // Because we don't double store the 'l'.
    /// assert_eq!(s.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    /// ```
    /// # use std::str::FromStr;
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::from_str("hello").unwrap();
    /// let s2 = CharSet::default();
    ///
    /// assert!(!s1.is_empty());
    /// assert!(s2.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }
    /// Returns true if this set contains a value.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let a = Alpha::try_from('a').unwrap();
    /// assert!(!s.contains(a));
    ///
    /// s.insert(a);
    /// assert!(s.contains(a));
    /// ```
    #[inline]
    pub fn contains<T: AsRef<Alpha>>(&self, value: T) -> bool {
        self.0 & (1 << u8::from(value.as_ref())) > 0
    }

    /// Returns true if this set contains a value from a char.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let a = Alpha::try_from('a').unwrap();
    /// assert!(!s.try_contains('a').unwrap());
    ///
    /// s.insert(a);
    /// assert!(s.try_contains('a').unwrap());
    /// ```
    pub fn try_contains(&self, value: char) -> Result<bool, CharSetError> {
        Ok(Alpha::try_from(value).map(|a| self.contains(a))?)
    }

    /// Adds a value to the set.
    ///
    /// Unlike with the normal HashSet, this will add this value to the set
    /// regardless of whether or not it already existed.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let a = Alpha::try_from('a').unwrap();
    /// assert!(!s.contains(a));
    ///
    /// s.insert(a);
    /// assert!(s.contains(a));
    /// ```
    #[inline]
    pub fn insert<T: Into<Alpha>>(&mut self, value: T) {
        self.0 |= 1 << u8::from(value.into());
    }

    /// Attempt to add a value corresponding to a `char` to the set.
    ///
    /// This will error if the passed char is not an ascii alpha.
    ///
    /// Unlike with the normal HashSet, this will add this value to the set
    /// regardless of whether or not it already existed.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let a = Alpha::try_from('a').unwrap();
    /// assert!(!s.contains(a));
    ///
    /// s.try_insert('a').unwrap();
    /// assert!(s.contains(a));
    /// ```
    pub fn try_insert(&mut self, value: char) -> Result<(), CharSetError> {
        self.insert(Alpha::try_from(value)?);
        Ok(())
    }

    /// Remove a value from the set.
    ///
    /// Unlike with the normal HashSet, this will not indicate if the value
    /// already existed.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let c = Alpha::try_from('c').unwrap();
    /// assert!(!s.contains(c));
    ///
    /// s.insert(c);
    /// assert!(s.contains(c));
    ///
    /// s.remove(c);
    /// assert!(!s.contains(c));
    /// ```
    #[inline]
    pub fn remove<T: AsRef<Alpha>>(&mut self, value: T) {
        self.0 &= !(1 << u8::from(value.as_ref()))
    }

    /// Attempt to remove a value corresponding to a `char` from the set.
    ///
    /// This will error if the passed char is not an ascii alpha.
    ///
    /// Unlike with the normal HashSet, this will not indicate if the value
    /// already existed.
    ///
    /// # Examples
    /// ```
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let mut s = CharSet::default();
    ///
    /// let c = Alpha::try_from('c').unwrap();
    /// assert!(!s.contains(c));
    ///
    /// s.insert(c);
    /// assert!(s.contains(c));
    ///
    /// s.try_remove('c').unwrap();
    /// assert!(!s.contains(c));
    /// ```
    pub fn try_remove(&mut self, value: char) -> Result<(), CharSetError> {
        self.remove(Alpha::try_from(value)?);
        Ok(())
    }

    /// An iterator visiting all elements in alpha order with lowercase first.
    ///
    /// Unlike with HashSet, this returns an owned [Iterator].
    ///
    /// # Examples
    /// ```
    /// # use std::ops::Deref;
    /// # use aoc_types::Alpha;
    /// # use aoc_collections::CharSet;
    /// let s = CharSet::try_from("hello").unwrap();
    /// for a in s.iter() {
    ///     println!("{}", a.deref());
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = Alpha> {
        CharSetIterator {
            value: self.0,
            ..Default::default()
        }
    }

    /// Compute the union between this set and `other`.
    ///
    /// Unlike with HashSet, this returns another `CharSet` of the union.
    ///
    /// This is equivalent to `self | other`.
    ///
    /// # Examples
    /// ```
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::try_from("hello").unwrap();
    /// let s2 = CharSet::try_from("world").unwrap();
    ///
    /// let s3 = s1.union(s2);
    /// let expected = CharSet::try_from("helowrd").unwrap();
    /// assert_eq!(s3, expected);
    /// ```
    pub fn union<T: AsRef<CharSet>>(&self, other: T) -> Self {
        *self | *other.as_ref()
    }

    /// Compute the intersection between this set and `other`.
    ///
    /// Unlike with HashSet, this returns another `CharSet` of the union.
    ///
    /// This is equivalent to `self & other`.
    ///
    /// # Examples
    /// ```
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::try_from("hello").unwrap();
    /// let s2 = CharSet::try_from("world").unwrap();
    ///
    /// let s3 = s1.intersection(s2);
    /// let expected = CharSet::try_from("ol").unwrap();
    /// assert_eq!(s3, expected);
    /// ```
    pub fn intersection<T: AsRef<CharSet>>(&self, other: T) -> Self {
        *self & *other.as_ref()
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    ///
    /// # Examples
    /// ```
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::try_from("hello").unwrap();
    /// let s2 = CharSet::try_from("world").unwrap();
    /// let s3 = CharSet::try_from("fine").unwrap();
    ///
    /// assert!(!s1.is_disjoint(s3));
    /// assert!(s2.is_disjoint(s3));
    /// ```
    pub fn is_disjoint<T: AsRef<CharSet>>(&self, other: T) -> bool {
        self.0 & other.as_ref().0 == 0
    }

    /// Returns `true` if the set is a subset of `other`, i.e. `other` contains
    /// at least all the values in `self`.
    ///
    /// # Examples
    /// ```
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::try_from("hello").unwrap();
    /// let s2 = CharSet::try_from("ll").unwrap();
    ///
    /// assert!(!s1.is_subset(&s2));
    /// assert!(s2.is_subset(&s1));
    /// ```
    pub fn is_subset<T: AsRef<CharSet>>(&self, other: T) -> bool {
        *self == *self & *other.as_ref()
    }

    /// Returns `true` if the set is a superset of `other`, i.e. `self` contains
    /// at least all the values in `other`.
    ///
    /// # Examples
    /// ```
    /// # use aoc_collections::CharSet;
    /// let s1 = CharSet::try_from("hello").unwrap();
    /// let s2 = CharSet::try_from("ll").unwrap();
    ///
    /// assert!(s1.is_superset(&s2));
    /// assert!(!s2.is_superset(&s1));
    /// ```
    pub fn is_superset<T: AsRef<CharSet>>(&self, other: T) -> bool {
        other.as_ref().is_subset(self)
    }
}

impl AsRef<CharSet> for CharSet {
    fn as_ref(&self) -> &CharSet {
        self
    }
}

impl TryFrom<String> for CharSet {
    type Error = CharSetError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.as_str().try_into()
    }
}

impl TryFrom<&str> for CharSet {
    type Error = CharSetError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let mut s = Self::default();

        for ch in value.chars() {
            s.insert(Alpha::try_from(ch)?);
        }

        Ok(s)
    }
}

impl FromStr for CharSet {
    type Err = CharSetError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.try_into()
    }
}

impl FromIterator<Alpha> for CharSet {
    fn from_iter<T: IntoIterator<Item = Alpha>>(iter: T) -> Self {
        let mut s = Self::default();
        for a in iter {
            s.insert(a);
        }

        s
    }
}

impl FromIterator<LowerAlpha> for CharSet {
    fn from_iter<T: IntoIterator<Item = LowerAlpha>>(iter: T) -> Self {
        let mut s = Self::default();
        for a in iter {
            s.insert(Alpha::from(a));
        }

        s
    }
}

impl FromIterator<UpperAlpha> for CharSet {
    fn from_iter<T: IntoIterator<Item = UpperAlpha>>(iter: T) -> Self {
        let mut s = Self::default();
        for a in iter {
            s.insert(Alpha::from(a));
        }

        s
    }
}

impl BitOr for CharSet {
    type Output = CharSet;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for CharSet {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}

impl BitAnd for CharSet {
    type Output = CharSet;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for CharSet {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}

impl BitXor for CharSet {
    type Output = CharSet;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for CharSet {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}

impl IntoIterator for CharSet {
    type Item = Alpha;
    type IntoIter = CharSetIterator;

    fn into_iter(self) -> Self::IntoIter {
        CharSetIterator {
            value: self.0,
            ..Default::default()
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharSetIterator {
    value: u64,
    cur_shift: u32,
}

impl Iterator for CharSetIterator {
    type Item = Alpha;

    fn next(&mut self) -> Option<Self::Item> {
        if self.value == 0 || self.cur_shift > 51 {
            None
        } else {
            let shift_amt = self.value.trailing_zeros();
            // one extra because we want that 1 to be shifted off
            self.value >>= shift_amt + 1;
            self.cur_shift += shift_amt;
            // we know this won't overflow because the worst this could be is
            // 64, which should already be impossible
            let ch = num_to_ascii_alpha(self.cur_shift as u8);
            // move over the current letter
            self.cur_shift += 1;

            // We _shouldn't_ have an error at all, so just convert the result
            // to an option
            Alpha::try_from(ch).ok()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn iteration() {
        let input = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        let s = CharSet::from_str(input).unwrap();

        // sanity
        assert_eq!(s.len(), 52);

        let alphas: Vec<_> = s.into_iter().collect();
        assert_eq!(alphas.len(), 52);

        let expected = input
            .chars()
            .map(Alpha::try_from)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        assert_eq!(alphas, expected);

        let input = "HelloWorld";
        let s = CharSet::from_str(input).unwrap();

        // sanity
        assert_eq!(s.len(), 7);

        let alphas: HashSet<_> = s.into_iter().collect();
        assert_eq!(alphas.len(), 7);

        let expected = input
            .chars()
            .map(Alpha::try_from)
            .collect::<Result<HashSet<_>, _>>()
            .unwrap();

        assert_eq!(alphas, expected);
    }

    #[test]
    fn iter() {
        let input = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        let s = CharSet::from_str(input).unwrap();

        // sanity
        assert_eq!(s.len(), 52);

        let alphas: Vec<_> = s.iter().collect();
        assert_eq!(alphas.len(), 52);

        let expected = input
            .chars()
            .map(Alpha::try_from)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        assert_eq!(alphas, expected);

        let input = "HelloWorld";
        let s = CharSet::from_str(input).unwrap();

        // sanity
        assert_eq!(s.len(), 7);

        let alphas: HashSet<_> = s.iter().collect();
        assert_eq!(alphas.len(), 7);

        let expected = input
            .chars()
            .map(Alpha::try_from)
            .collect::<Result<HashSet<_>, _>>()
            .unwrap();

        assert_eq!(alphas, expected);
    }

    #[test]
    fn bit_or() {
        let mut s1 = CharSet::from_str("hello").unwrap();
        let s2 = CharSet::from_str("world").unwrap();
        let expected = CharSet::from_str("helorwd").unwrap();

        let s3 = s1 | s2;
        assert_eq!(s3, expected);
        assert_eq!(s1.union(s2), expected);

        s1 |= s2;
        assert_eq!(s1, expected);
    }

    #[test]
    fn bit_and() {
        let mut s1 = CharSet::from_str("hello").unwrap();
        let s2 = CharSet::from_str("world").unwrap();
        let expected = CharSet::from_str("ol").unwrap();

        let s3 = s1 & s2;
        assert_eq!(s3, expected);
        assert_eq!(s1.intersection(s2), expected);

        s1 &= s2;
        assert_eq!(s1, expected);
    }

    #[test]
    fn bit_xor() {
        let mut s1 = CharSet::from_str("hello").unwrap();
        let s2 = CharSet::from_str("world").unwrap();
        let expected = CharSet::from_str("hwerd").unwrap();

        let s3 = s1 ^ s2;
        assert_eq!(s3, expected);

        s1 ^= s2;
        assert_eq!(s1, expected);
    }
}
