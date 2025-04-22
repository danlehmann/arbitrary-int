use core::fmt::Debug;
use crate::TryNewError;

pub(crate) mod sealed {
    /// Ensures that outside users can not implement the traits provided by this crate.
    #[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
    pub trait Sealed {}
}

/// The base trait for integer numbers, either built-in (u8, i8, u16, i16, u32, i32, u64, i64,
/// u128, i128) or arbitrary-int (u1, i1, u7, i7 etc.).
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait Integer: Sized + Copy + Clone + PartialOrd + Ord + PartialEq + Eq + sealed::Sealed {
    type UnderlyingType: Integer
    + Debug
    + TryFrom<u8>
    + TryFrom<u16>
    + TryFrom<u32>
    + TryFrom<u64>
    + TryFrom<u128>;

    /// Number of bits that can fit in this type
    const BITS: usize;

    /// Minimum value that can be represented by this type
    const MIN: Self;

    /// Maximum value that can be represented by this type
    const MAX: Self;

    /// Creates a number from the given value, throwing an error if the value is too large.
    /// This constructor is useful when creating a value from a literal.
    fn new(value: Self::UnderlyingType) -> Self;

    /// Creates a number from the given value, return None if the value is too large
    fn try_new(value: Self::UnderlyingType) -> Result<Self, TryNewError>;

    fn value(self) -> Self::UnderlyingType;

    /// Creates a number from the given value, throwing an error if the value is too large.
    /// This constructor is useful when the value is convertible to T. Use [`Self::new`] for literals.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn from_<T: Integer>(value: T) -> Self;

    /// Creates an instance from the given `value`. Unlike the various `new...` functions, this
    /// will never fail as the value is masked to the result size.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn masked_new<T: Integer>(value: T) -> Self;

    fn as_u8(self) -> u8;

    fn as_u16(self) -> u16;

    fn as_u32(self) -> u32;

    fn as_u64(self) -> u64;

    fn as_u128(self) -> u128;

    fn as_usize(self) -> usize;

    fn as_i8(self) -> i8;

    fn as_i16(self) -> i16;

    fn as_i32(self) -> i32;

    fn as_i64(self) -> i64;

    fn as_i128(self) -> i128;

    fn as_isize(self) -> isize;

    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    #[inline]
    fn as_<T: Integer>(self) -> T {
        T::masked_new(self)
    }
}

/// The base trait for all signed numbers, either built-in (i8, i16, i32, i64, i128) or
/// arbitrary-int (i1, i7 etc.).
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait SignedInteger: Integer {}

/// The base trait for all unsigned numbers, either built-in (u8, u16, u32, u64, u128) or
/// arbitrary-int (u1, u7 etc.).
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait UnsignedInteger: Integer {}

