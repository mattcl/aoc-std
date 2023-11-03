//! This module contains common structures and functions for handling VM-related
//! AoC problems.
//!
//! Commonly, we're asked to handle value types that can be eitehr literals or
//! pointers to registers. This module exposes some generics and defaults for
//! those things.
use thiserror::Error;

mod register;
mod value;

pub use register::{RegisterIndex, Registers, StandardRegisters};
pub use value::{StandardValue, Value};

#[derive(Debug, Error)]
pub enum VmError {
    #[error("Register index out of bounds: {0}")]
    RegisterOutOfBounds(usize),

    #[error("The input: '{0}' is not a valid StandardValue")]
    StandardValueParseError(String),
}
