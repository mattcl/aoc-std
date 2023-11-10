use std::ops::Deref;

use aoc_conversions::chars::{
    ascii_alpha_to_num, ascii_lowercase_alpha_to_num, ascii_uppercase_alpha_to_num,
};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Error)]
#[non_exhaustive]
pub enum AlphaError {
    #[error("Invalid character: '{0}'")]
    InvalidCharacter(char),
}

/// A representation of an ascii alpha char from `'a'..='z'` and `'A'..='Z'`.
///
/// This is to allow for front-loading validity checking by providing a more
/// restrictive type than simply [char], while still allowing deref to [char].
///
/// This also allows for consistent conversions of [Alpha] to [u8], where
/// `'a'..='z'` is `0..=25` and `'A'..='Z'` is `26..=51`.
///
/// Example:
///
/// ```
/// # use aoc_types::Alpha;
/// let a = Alpha::try_from('a').unwrap();
/// assert_eq!(*a, 'a');
///
/// assert!(Alpha::try_from(' ').is_err());
///
/// let d = Alpha::try_from('D').unwrap();
/// assert_eq!(u8::from(d), 29);
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Alpha(char);

impl Deref for Alpha {
    type Target = char;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Alpha> for Alpha {
    fn as_ref(&self) -> &Alpha {
        self
    }
}

impl TryFrom<char> for Alpha {
    type Error = AlphaError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        if value.is_ascii_alphabetic() {
            Ok(Self(value))
        } else {
            Err(AlphaError::InvalidCharacter(value))
        }
    }
}

impl From<LowerAlpha> for Alpha {
    fn from(value: LowerAlpha) -> Self {
        Alpha(value.0)
    }
}

impl From<&LowerAlpha> for Alpha {
    fn from(value: &LowerAlpha) -> Self {
        Alpha(value.0)
    }
}

impl From<UpperAlpha> for Alpha {
    fn from(value: UpperAlpha) -> Self {
        Alpha(value.0)
    }
}

impl From<&UpperAlpha> for Alpha {
    fn from(value: &UpperAlpha) -> Self {
        Alpha(value.0)
    }
}

impl From<Alpha> for u8 {
    fn from(value: Alpha) -> Self {
        ascii_alpha_to_num(*value)
    }
}

impl From<&Alpha> for u8 {
    fn from(value: &Alpha) -> Self {
        ascii_alpha_to_num(**value)
    }
}

impl From<Alpha> for char {
    fn from(value: Alpha) -> Self {
        value.0
    }
}

impl From<&Alpha> for char {
    fn from(value: &Alpha) -> Self {
        value.0
    }
}

/// A representation of an ascii lower alpha char from `'a'..='z'`.
///
/// This is to allow for front-loading validity checking by providing a more
/// restrictive type than simply [char], while still allowing deref to [char].
///
/// This also allows for consistent conversions of [LowerAlpha] to [u8], where
/// `'a'..='z'` is `0..=25`.
///
/// Example:
///
/// ```
/// # use aoc_types::LowerAlpha;
/// let a = LowerAlpha::try_from('a').unwrap();
/// assert_eq!(*a, 'a');
///
/// assert!(LowerAlpha::try_from(' ').is_err());
///
/// let d = LowerAlpha::try_from('d').unwrap();
/// assert_eq!(u8::from(d), 3);
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LowerAlpha(char);

impl Deref for LowerAlpha {
    type Target = char;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<LowerAlpha> for LowerAlpha {
    fn as_ref(&self) -> &LowerAlpha {
        self
    }
}

impl TryFrom<char> for LowerAlpha {
    type Error = AlphaError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        if value.is_ascii_lowercase() {
            Ok(Self(value))
        } else {
            Err(AlphaError::InvalidCharacter(value))
        }
    }
}

impl From<LowerAlpha> for u8 {
    fn from(value: LowerAlpha) -> Self {
        ascii_lowercase_alpha_to_num(*value)
    }
}

impl From<&LowerAlpha> for u8 {
    fn from(value: &LowerAlpha) -> Self {
        ascii_lowercase_alpha_to_num(**value)
    }
}

impl From<LowerAlpha> for char {
    fn from(value: LowerAlpha) -> Self {
        value.0
    }
}

impl From<&LowerAlpha> for char {
    fn from(value: &LowerAlpha) -> Self {
        value.0
    }
}

/// A representation of an ascii upper alpha char from `'A'..='Z'`.
///
/// This is to allow for front-loading validity checking by providing a more
/// restrictive type than simply [char], while still allowing deref to [char].
///
/// This also allows for consistent conversions of [UpperAlpha] to [u8], where
/// `'A'..='Z'` is `26..=51`.
///
/// Example:
///
/// ```
/// # use aoc_types::UpperAlpha;
/// let a = UpperAlpha::try_from('A').unwrap();
/// assert_eq!(*a, 'A');
///
/// assert!(UpperAlpha::try_from('a').is_err());
///
/// let d = UpperAlpha::try_from('D').unwrap();
/// assert_eq!(u8::from(d), 29);
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UpperAlpha(char);

impl Deref for UpperAlpha {
    type Target = char;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<UpperAlpha> for UpperAlpha {
    fn as_ref(&self) -> &UpperAlpha {
        self
    }
}

impl TryFrom<char> for UpperAlpha {
    type Error = AlphaError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        if value.is_ascii_uppercase() {
            Ok(Self(value))
        } else {
            Err(AlphaError::InvalidCharacter(value))
        }
    }
}

impl From<UpperAlpha> for u8 {
    fn from(value: UpperAlpha) -> Self {
        ascii_uppercase_alpha_to_num(*value)
    }
}

impl From<&UpperAlpha> for u8 {
    fn from(value: &UpperAlpha) -> Self {
        ascii_uppercase_alpha_to_num(**value)
    }
}

impl From<UpperAlpha> for char {
    fn from(value: UpperAlpha) -> Self {
        value.0
    }
}

impl From<&UpperAlpha> for char {
    fn from(value: &UpperAlpha) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    mod alpha {
        use super::super::*;

        #[test]
        fn conversion() {
            for (idx, ch) in ('a'..='z').chain('A'..='Z').enumerate() {
                assert_eq!(Alpha::try_from(ch).unwrap(), Alpha(ch));
                assert_eq!(u8::from(Alpha(ch)), idx as u8);

                if ch.is_lowercase() {
                    assert_eq!(Alpha::from(LowerAlpha(ch)), Alpha(ch));
                } else {
                    assert_eq!(Alpha::from(UpperAlpha(ch)), Alpha(ch));
                }
            }

            assert!(Alpha::try_from('0').is_err());
            assert!(Alpha::try_from(' ').is_err());
            assert!(Alpha::try_from('!').is_err());
        }
    }

    mod lower_alpha {
        use super::super::*;

        #[test]
        fn conversion() {
            for (idx, ch) in ('a'..='z').enumerate() {
                assert_eq!(LowerAlpha::try_from(ch).unwrap(), LowerAlpha(ch));
                assert_eq!(u8::from(LowerAlpha(ch)), idx as u8);
            }

            assert!(LowerAlpha::try_from('A').is_err());
            assert!(LowerAlpha::try_from('0').is_err());
            assert!(LowerAlpha::try_from(' ').is_err());
            assert!(LowerAlpha::try_from('!').is_err());
        }
    }

    mod upper_alpha {
        use super::super::*;

        #[test]
        fn conversion() {
            for (idx, ch) in ('A'..='Z').enumerate() {
                assert_eq!(UpperAlpha::try_from(ch).unwrap(), UpperAlpha(ch));
                assert_eq!(u8::from(UpperAlpha(ch)), idx as u8 + 26);
            }

            assert!(UpperAlpha::try_from('a').is_err());
            assert!(UpperAlpha::try_from('0').is_err());
            assert!(UpperAlpha::try_from(' ').is_err());
            assert!(UpperAlpha::try_from('!').is_err());
        }
    }
}
