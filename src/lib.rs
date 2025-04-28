#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(
    feature = "const_convert_and_const_trait_impl",
    feature(const_convert, const_trait_impl, inline_const)
)]
#![cfg_attr(feature = "step_trait", feature(step_trait))]

#[cfg(all(feature = "borsh", not(feature = "std")))]
extern crate alloc;

use core::fmt;

mod common;
mod signed;
pub mod traits;
mod unsigned;
mod v1_number_compat;

pub use signed::*;
pub use unsigned::*;
pub use v1_number_compat::*;

/// The preferred way to import arbitrary-int into a project: `use arbitrary_int::prelude::*`
pub mod prelude {
    pub use crate::signed::*;
    pub use crate::traits::*;
    pub use crate::unsigned::*;
    pub use crate::TryNewError;
}

#[cfg(feature = "arbitrary")]
mod arbitrary;

#[cfg(feature = "quickcheck")]
mod quickcheck;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TryNewError;

impl fmt::Display for TryNewError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value too large to fit within this integer type")
    }
}
