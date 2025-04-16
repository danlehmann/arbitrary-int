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
mod unsigned;

pub use common::Integer;
pub use signed::*;
pub use unsigned::*;

/// Compatibility with arbitrary-int 1.x, which didn't support signed integers.
///
/// Going forward, use [`UnsignedInteger`] (to allow only unsigned integers) or [`Integer`] (to
/// support either signed or unsigned)
#[deprecated(since = "2.0", note = "Use [`UnsignedInteger`] or [`Integer`] instead")]
pub trait Number: UnsignedInteger {}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TryNewError;

impl fmt::Display for TryNewError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value too large to fit within this integer type")
    }
}
