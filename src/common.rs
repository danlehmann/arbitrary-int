//! This module contains the functionality that can be shared between [`crate::Int`] and [`crate::UInt`]

use crate::TryNewError;
use core::fmt::Debug;

/// Copies LEN bytes from `from[FROM_OFFSET]` to `to[TO_OFFSET]`.
///
/// Usable in const contexts and inlines for small arrays.
#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
#[inline(always)]
pub(crate) const fn const_byte_copy<
    const LEN: usize,
    const TO_OFFSET: usize,
    const FROM_OFFSET: usize,
>(
    to: &mut [u8],
    from: &[u8],
) {
    let mut i = 0;
    while i < LEN {
        to[TO_OFFSET + i] = from[FROM_OFFSET + i];
        i += 1;
    }
}

#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait Integer: Sized + Copy + Clone + PartialOrd + Ord + PartialEq + Eq {
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

    fn as_u8(&self) -> u8;

    fn as_u16(&self) -> u16;

    fn as_u32(&self) -> u32;

    fn as_u64(&self) -> u64;

    fn as_u128(&self) -> u128;

    fn as_usize(&self) -> usize;

    fn as_i8(&self) -> i8;

    fn as_i16(&self) -> i16;

    fn as_i32(&self) -> i32;

    fn as_i64(&self) -> i64;

    fn as_i128(&self) -> i128;

    fn as_isize(&self) -> isize;

    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    #[inline]
    fn as_<T: Integer>(self) -> T {
        T::masked_new(self)
    }
}

// Define type aliases like u1, u63 and u80 (and their signed equivalents) using the smallest possible underlying data type.
// These are for convenience only - UInt<u32, 15> is still legal
macro_rules! type_alias {
    ($ty:ident($storage:ty), $(($name:ident, $bits:expr)),+) => {
        $( pub type $name = crate::$ty<$storage, $bits>; )+
    }
}

pub(crate) use type_alias;

// Conversions
#[cfg(feature = "const_convert_and_const_trait_impl")]
macro_rules! from_arbitrary_int_impl {
    ($ty:ident($from:ty), [$($into:ty),+]) => {
        $(
            impl<const BITS: usize, const BITS_FROM: usize> const From<$ty<$from, BITS_FROM>> for $ty<$into, BITS> {
                #[inline]
                fn from(item: $ty<$from, BITS_FROM>) -> Self {
                    const { assert!(BITS_FROM <= BITS, "Can not call from() to convert between the given bit widths.") };
                    Self { value: item.value as $into }
                }
            }
        )+
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
macro_rules! from_arbitrary_int_impl {
    ($ty:ident($from:ty), [$($into:ty),+]) => {
        $(
            impl<const BITS: usize, const BITS_FROM: usize> From<$ty<$from, BITS_FROM>> for $ty<$into, BITS> {
                #[inline]
                fn from(item: $ty<$from, BITS_FROM>) -> Self {
                    const { assert!(BITS_FROM <= BITS, "Can not call from() to convert between the given bit widths.") };
                    Self { value: item.value as $into }
                }
            }
        )+
    };
}

pub(crate) use from_arbitrary_int_impl;

#[cfg(feature = "const_convert_and_const_trait_impl")]
macro_rules! from_native_impl {
    ($ty:ident($from:ty), [$($into:ty),+]) => {
        $(
            impl<const BITS: usize> const From<$from> for $ty<$into, BITS> {
                #[inline]
                fn from(from: $from) -> Self {
                    const { assert!(<$from>::BITS as usize <= BITS, "Can not call from() to convert between the given bit widths.") };
                    Self { value: from as $into }
                }
            }

            impl<const BITS: usize> const From<$ty<$from, BITS>> for $into {
                #[inline]
                fn from(from: $ty<$from, BITS>) -> Self {
                    const { assert!(BITS <= <$from>::BITS as usize, "Can not call from() to convert between the given bit widths.") };
                    from.value as $into
                }
            }
        )+
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
macro_rules! from_native_impl {
    ($ty:ident($from:ty), [$($into:ty),+]) => {
        $(
            impl<const BITS: usize> From<$from> for $ty<$into, BITS> {
                #[inline]
                fn from(from: $from) -> Self {
                    const { assert!(<$from>::BITS as usize <= BITS, "Can not call from() to convert between the given bit widths.") };
                    Self { value: from as $into }
                }
            }

            impl<const BITS: usize> From<$ty<$from, BITS>> for $into {
                #[inline]
                fn from(from: $ty<$from, BITS>) -> Self {
                    const { assert!(BITS <= <$from>::BITS as usize, "Can not call from() to convert between the given bit widths.") };
                    from.value as $into
                }
            }
        )+
    };
}

pub(crate) use from_native_impl;

macro_rules! impl_extract {
    (
        $base_type:ty,
        $example:literal,
        |$value:ident| $constructor:expr,
        $(($bits:literal, $(($type:ty, $extract_fn:ident)),+)),+
    ) => {
        $($(
            #[doc = concat!("Extracts bits from a given value, starting from `start_bit`. This is equivalent to: `", $example, "`.")]
            /// Unlike [`new`](Self::new), this function doesn't perform range-checking and is slightly more efficient.
            ///
            /// # Panics
            ///
            #[doc = concat!(" Panics if `start_bit + Self::BITS` doesn't fit within an ", stringify!($type), ", i.e. it is greater than ", stringify!($bits), ".")]
            #[inline]
            pub const fn $extract_fn(value: $type, start_bit: usize) -> Self {
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;
                assert!(start_bit + BITS <= $bits);

                let $value = (value >> start_bit) as $base_type;
                Self { value: $constructor }
            }
        )+)+
    };
}

pub(crate) use impl_extract;

macro_rules! bytes_operation_impl {
    ($target:ty, $base_data_type:ty) => {
        #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
        impl $target {
            /// Reverses the byte order of the integer.
            #[inline]
            pub const fn swap_bytes(&self) -> Self {
                // swap_bytes() of the underlying type does most of the work. Then, we just need to shift
                Self {
                    value: self.value.swap_bytes() >> Self::UNUSED_BITS,
                }
            }

            pub const fn to_le_bytes(&self) -> [u8; Self::BITS >> 3] {
                let mut result = [0_u8; Self::BITS >> 3];
                let be = self.value.to_le_bytes();
                crate::common::const_byte_copy::<{ Self::BITS >> 3 }, 0, 0>(&mut result, &be);
                result
            }

            pub const fn to_be_bytes(&self) -> [u8; Self::BITS >> 3] {
                let mut result = [0_u8; Self::BITS >> 3];
                let be = self.value.to_be_bytes();
                crate::common::const_byte_copy::<{ Self::BITS >> 3 }, 0, { Self::UNUSED_BITS >> 3 }>(
                    &mut result,
                    &be,
                );
                result
            }

            pub const fn from_le_bytes(from: [u8; Self::BITS >> 3]) -> Self {
                let mut bytes = [0_u8; core::mem::size_of::<$base_data_type>()];
                crate::common::const_byte_copy::<{ Self::BITS >> 3 }, { Self::UNUSED_BITS >> 3 }, 0>(
                    &mut bytes, &from,
                );
                Self {
                    value: <$base_data_type>::from_le_bytes(bytes) >> Self::UNUSED_BITS,
                }
            }

            pub const fn from_be_bytes(from: [u8; Self::BITS >> 3]) -> Self {
                let mut bytes = [0_u8; core::mem::size_of::<$base_data_type>()];
                crate::common::const_byte_copy::<{ Self::BITS >> 3 }, 0, 0>(&mut bytes, &from);
                Self {
                    value: <$base_data_type>::from_be_bytes(bytes) >> Self::UNUSED_BITS,
                }
            }

            #[inline]
            pub const fn to_ne_bytes(&self) -> [u8; Self::BITS >> 3] {
                #[cfg(target_endian = "little")]
                {
                    self.to_le_bytes()
                }
                #[cfg(target_endian = "big")]
                {
                    self.to_be_bytes()
                }
            }

            #[inline]
            pub const fn from_ne_bytes(bytes: [u8; Self::BITS >> 3]) -> Self {
                #[cfg(target_endian = "little")]
                {
                    Self::from_le_bytes(bytes)
                }
                #[cfg(target_endian = "big")]
                {
                    Self::from_be_bytes(bytes)
                }
            }

            #[inline]
            pub const fn to_le(self) -> Self {
                #[cfg(target_endian = "little")]
                {
                    self
                }
                #[cfg(target_endian = "big")]
                {
                    self.swap_bytes()
                }
            }

            #[inline]
            pub const fn to_be(self) -> Self {
                #[cfg(target_endian = "little")]
                {
                    self.swap_bytes()
                }
                #[cfg(target_endian = "big")]
                {
                    self
                }
            }

            #[inline]
            pub const fn from_le(value: Self) -> Self {
                value.to_le()
            }

            #[inline]
            pub const fn from_be(value: Self) -> Self {
                value.to_be()
            }
        }
    };
}

pub(crate) use bytes_operation_impl;
