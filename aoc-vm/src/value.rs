use std::{fmt::Display, str::FromStr};

use aoc_types::LowerAlpha;
use nom::{
    branch::alt,
    character::complete,
    combinator::{all_consuming, map_res},
    IResult,
};

use crate::{RegisterIndex, Registers, VmError};

/// A representation of the Value component of an operation.
///
/// This can be either a literal (`L`) or a value that indicates a particular
/// register (`R`) (like a char or usize).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value<L, R> {
    Literal(L),
    Register(R),
}

impl<L, R> Display for Value<L, R>
where
    L: Display,
    R: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(v) => write!(f, "Lit: {}", v),
            Self::Register(r) => write!(f, "Reg: {}", r),
        }
    }
}

impl<L, R> Value<L, R>
where
    L: Copy,
    R: Copy + Into<RegisterIndex>,
{
    // Get the literal value this Value contains or the literal value
    // referenced by this Value's register pointer.
    //
    // This will return an error if this is the `Register` variant and the
    // register points at a location in `registers` that does not exist.
    pub fn get<const N: usize>(&self, registers: &Registers<L, N>) -> Result<L, VmError> {
        match self {
            Self::Literal(v) => Ok(*v),
            Self::Register(r) => registers.get(*r),
        }
    }
}

/// A "standard" [Value] type of `Value<i64, LowerAlpha>`.
pub type StandardValue = Value<i64, LowerAlpha>;

impl StandardValue {
    /// A `nom` parser that can parse a [StandardValue] from an input `&str`.
    ///
    /// This parser only requires that the input string leads with a valid
    /// `Standardvalue`.
    pub fn parser(input: &str) -> IResult<&str, StandardValue> {
        alt((literal_parser, lower_alpha_register_parser))(input)
    }
}

impl FromStr for StandardValue {
    type Err = VmError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // we require the string be completely consumed in this case
        let (_, v) = all_consuming(Self::parser)(s)
            .map_err(|_| VmError::StandardValueParseError(s.to_string()))?;

        Ok(v)
    }
}

/// helper parser for parsing the Literal variant of StandardValue
fn literal_parser(input: &str) -> IResult<&str, StandardValue> {
    let (input, val) = complete::i64(input)?;

    Ok((input, StandardValue::Literal(val)))
}

/// helper parser for parsing the Register variant of StandardValue
fn lower_alpha_register_parser(input: &str) -> IResult<&str, StandardValue> {
    let (input, val) = map_res(complete::anychar, |c: char| c.try_into())(input)?;

    Ok((input, StandardValue::Register(val)))
}

#[cfg(test)]
mod tests {
    mod standard_value {
        use super::super::*;

        #[test]
        fn parsing() {
            let (_, v) = StandardValue::parser("-123 a 15").unwrap();
            assert_eq!(v, StandardValue::Literal(-123));

            let (_, v) = StandardValue::parser("0").unwrap();
            assert_eq!(v, StandardValue::Literal(0));

            // this would be invalid in most cases, but in the context of the
            // parser doing what it says, this is correct
            let (_, v) = StandardValue::parser("doof").unwrap();
            assert_eq!(v, StandardValue::Register('d'.try_into().unwrap()));

            // on the other hand, parsing from_str requires the input be fully
            // consumed
            let v = StandardValue::from_str("d").unwrap();
            assert_eq!(v, StandardValue::Register('d'.try_into().unwrap()));

            assert!(StandardValue::from_str("doof").is_err());

            assert!(StandardValue::parser("").is_err());
            assert!(StandardValue::parser("A").is_err());
        }

        #[test]
        fn literal_extraction() {
            let ch = LowerAlpha::try_from('c').unwrap();
            let mut registers: Registers<i64, 10> = Registers::default();
            registers.set(ch, -12).unwrap();

            let v = StandardValue::Literal(10);
            assert_eq!(v.get(&registers).unwrap(), 10);

            let v = StandardValue::Register(ch);
            assert_eq!(v.get(&registers).unwrap(), -12);
        }
    }
}
