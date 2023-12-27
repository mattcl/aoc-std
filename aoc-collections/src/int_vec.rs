use std::{
    ops::{Deref, DerefMut},
    str::FromStr,
};

use nom::{
    character::complete::{self, multispace1},
    multi::separated_list1,
    IResult,
};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Error)]
pub enum IntVecError {
    #[error("failed to parse: {0}")]
    Parse(String),
}

/// A dumb wrapper around a `Vec<i64>` that can be efficiently constructed from
/// a newline-separated string.
///
/// # Examples
/// ```
/// use std::str::FromStr;
/// use aoc_collections::IntVec;
///
/// let input = r#"100
/// 200
/// 300
/// -100
/// 50"#;
///
/// let v = IntVec::from_str(input).unwrap();
/// assert_eq!(*v, vec![100_i64, 200, 300, -100, 50]);
///
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntVec(Vec<i64>);

impl Deref for IntVec {
    type Target = Vec<i64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for IntVec {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<Vec<i64>> for IntVec {
    fn from(value: Vec<i64>) -> Self {
        Self(value)
    }
}

impl TryFrom<&str> for IntVec {
    type Error = IntVecError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let (_, res) = parse_vec(value).map_err(|e| IntVecError::Parse(e.to_string()))?;

        Ok(res.into())
    }
}

impl FromStr for IntVec {
    type Err = IntVecError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.try_into()
    }
}

fn parse_vec(input: &str) -> IResult<&str, Vec<i64>> {
    separated_list1(multispace1, complete::i64)(input)
}
