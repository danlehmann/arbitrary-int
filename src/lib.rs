#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(
    feature = "const_convert_and_const_trait_impl",
    feature(const_convert, const_trait_impl, inline_const)
)]
#![cfg_attr(feature = "step_trait", feature(step_trait))]

#[cfg(all(feature = "borsh", not(feature = "std")))]
extern crate alloc;
extern crate core;

use core::fmt;

mod common;
mod signed;
mod unsigned;

pub use common::Number;
pub use signed::*;
pub use unsigned::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TryNewError;

impl fmt::Display for TryNewError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value too large to fit within this integer type")
    }
}
