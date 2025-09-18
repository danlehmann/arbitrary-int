// By unconditionally declaring this crate as `no_std` we opt out of the standard library's prelude,
// which implicitly brings items like `Vec` and `String` into scope. Since we'd need to import those
// manually in case the `alloc` crate is used but the standard library isn't, we might as well keep
// things consistent and always manually import them.
#![no_std]
#![cfg_attr(
    feature = "const_convert_and_const_trait_impl",
    feature(const_convert, const_trait_impl, inline_const)
)]
#![cfg_attr(feature = "step_trait", feature(step_trait))]

// This makes it possible to use `std::` when the `std` feature is enabled, even though we're `no_std`.
#[cfg(feature = "std")]
extern crate std;

// The `alloc` crate is always usable when the standard library (i.e. the `std` feature) is enabled.
// The standard library re-exports collections from the `alloc` crate, but since this crate supports
// `alloc` without `std` its best to use `alloc` directly: that works both with and without `std`.
#[cfg(any(feature = "borsh", feature = "std"))]
extern crate alloc;

use core::fmt;

mod common;
#[cfg(all(doctest, not(feature = "const_convert_and_const_trait_impl")))]
pub mod doctest;
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
