use std::{fmt::Display, ops::Deref};

use aoc_types::LowerAlpha;

use crate::VmError;

/// This is a type to allow for specifying clearer constraints for registers.
///
/// The idea is that we can make our register storage generic over things that
/// can be converted to this type, allowing us to abstract some of The
/// implementeation details. It will deref to a [usize].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegisterIndex(usize);

impl From<usize> for RegisterIndex {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl From<LowerAlpha> for RegisterIndex {
    fn from(value: LowerAlpha) -> Self {
        Self(u8::from(value) as usize)
    }
}

impl Deref for RegisterIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A copyable collection of registers of size `N` storing `T`.
///
/// This provides support for safe setting/getting of register values indexed
/// by [RegisterIndex] or types that are `Into<RegisterIndex>`.
///
/// This can be thought of as a list of size `N`, where each ement is `T`. For
/// convenience, this derefs to `[T; N]`.
#[derive(Debug, Clone, Copy)]
pub struct Registers<T, const N: usize> {
    values: [T; N],
}

impl<T, const N: usize> Default for Registers<T, N>
where
    T: Default + Copy,
{
    fn default() -> Self {
        Self {
            values: [T::default(); N],
        }
    }
}

impl<T, const N: usize> Deref for Registers<T, N> {
    type Target = [T; N];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<T, const N: usize> Display for Registers<T, N>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = String::from("Registers:");

        for (idx, v) in self.values.iter().enumerate() {
            out.push_str(&format!("\n{:03}: {}", idx, v));
        }

        out.fmt(f)
    }
}

impl<T, const N: usize> Registers<T, N>
where
    T: Copy,
{
    /// Get the value specified by the given register.
    ///
    /// This has a fixed size.
    ///
    /// This will error of the resulting [RegisterIndex] is beyond the bounds of
    /// the registers.
    pub fn get<R: Into<RegisterIndex>>(&self, register: R) -> Result<T, VmError> {
        let index = register.into();
        if *index >= N {
            return Err(VmError::RegisterOutOfBounds(*index));
        }

        Ok(self.values[*index])
    }

    /// Set the specified value in the location specified by the given register.
    ///
    /// This will error if the resulting [RegisterIndex] is beyond the bounds of
    /// the registers.
    pub fn set<R: Into<RegisterIndex>>(&mut self, register: R, value: T) -> Result<(), VmError> {
        let index = register.into();
        if *index >= N {
            return Err(VmError::RegisterOutOfBounds(*index));
        }

        self.values[*index] = value;

        Ok(())
    }
}

/// A "standard" register set with a stored typed of `i64`.
pub type StandardRegisters<const N: usize> = Registers<i64, N>;

#[cfg(test)]
mod tests {
    mod registers {
        use super::super::*;

        #[test]
        fn basic_operations() {
            let mut r: Registers<i64, 5> = Registers::default();

            for i in 0..5 {
                assert_eq!(r.get(i).unwrap(), 0);
            }

            r.set(2, -5).unwrap();
            assert_eq!(r.get(2).unwrap(), -5);

            assert!(r.get(5).is_err());
            assert!(r.set(5, 1).is_err());
        }
    }
}
