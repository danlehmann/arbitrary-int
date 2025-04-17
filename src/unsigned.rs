use crate::common::{
    bytes_operation_impl, from_arbitrary_int_impl, from_native_impl, impl_extract, Integer,
};
use crate::TryNewError;
use core::fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex};
#[cfg(feature = "step_trait")]
use core::iter::Step;
#[cfg(feature = "num-traits")]
use core::num::Wrapping;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(all(feature = "borsh", not(feature = "std")))]
use alloc::{collections::BTreeMap, string::ToString};

#[cfg(all(feature = "borsh", feature = "std"))]
use std::{collections::BTreeMap, string::ToString};

#[cfg(feature = "schemars")]
use schemars::JsonSchema;

/// The base trait for all unsigned numbers, either built-in (u8, u16, u32, u64, u128) or
/// arbitrary-int (u1, u7 etc.).
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait UnsignedInteger: Integer {}

macro_rules! impl_integer_native {
    // `$const_keyword` is marked as an optional fragment here so that it can conditionally be put on the impl.
    // This macro will be invoked with `u8 as const, ...` if `const_convert_and_const_trait_impl` is enabled.
    ($($type:ident $(as $const_keyword:ident)?),+) => {
        $(
            #[allow(deprecated)]
            impl super::Number for $type {
                type UnderlyingType = $type;
            }

            impl $($const_keyword)? UnsignedInteger for $type {

            }

            impl $($const_keyword)? Integer for $type {
                type UnderlyingType = $type;
                const BITS: usize = Self::BITS as usize;
                const MIN: Self = Self::MIN;
                const MAX: Self = Self::MAX;

                #[inline]
                fn new(value: Self::UnderlyingType) -> Self { value }

                #[inline]
                fn try_new(value: Self::UnderlyingType) -> Result<Self, TryNewError> { Ok(value) }

                #[inline]
                fn value(self) -> Self::UnderlyingType { self }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                #[inline]
                fn from_<T: Integer>(value: T) -> Self {
                    if T::BITS > Self::BITS as usize {
                        assert!(value <= T::masked_new(Self::MAX));
                    }
                    Self::masked_new(value)
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                #[inline]
                fn masked_new<T: Integer>(value: T) -> Self {
                    // Primitive types don't need masking
                    match Self::BITS {
                        8 => value.as_u8() as Self,
                        16 => value.as_u16() as Self,
                        32 => value.as_u32() as Self,
                        64 => value.as_u64() as Self,
                        128 => value.as_u128() as Self,
                        _ => panic!("Unhandled Integer type")
                    }
                }

                #[inline]
                fn as_u8(&self) -> u8 { *self as u8 }

                #[inline]
                fn as_u16(&self) -> u16 { *self as u16 }

                #[inline]
                fn as_u32(&self) -> u32 { *self as u32 }

                #[inline]
                fn as_u64(&self) -> u64 { *self as u64 }

                #[inline]
                fn as_u128(&self) -> u128 { *self as u128 }

                #[inline]
                fn as_usize(&self) -> usize { *self as usize }

                #[inline]
                fn as_i8(&self) -> i8 { *self as i8 }

                #[inline]
                fn as_i16(&self) -> i16 { *self as i16 }

                #[inline]
                fn as_i32(&self) -> i32 { *self as i32 }

                #[inline]
                fn as_i64(&self) -> i64 { *self as i64 }

                #[inline]
                fn as_i128(&self) -> i128 { *self as i128 }

                #[inline]
                fn as_isize(&self) -> isize { *self as isize }
            }
        )+
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
impl_integer_native!(u8, u16, u32, u64, u128);

#[cfg(feature = "const_convert_and_const_trait_impl")]
impl_integer_native!(u8 as const, u16 as const, u32 as const, u64 as const, u128 as const);

#[derive(Copy, Clone, Eq, PartialEq, Default, Ord, PartialOrd, Hash)]
pub struct UInt<T, const BITS: usize> {
    value: T,
}

impl<T: Copy, const BITS: usize> UInt<T, BITS> {
    /// The number of bits in the underlying type that are not present in this type.
    const UNUSED_BITS: usize = (core::mem::size_of::<T>() << 3) - Self::BITS;

    pub const BITS: usize = BITS;

    /// Returns the type as a fundamental data type
    #[cfg(not(feature = "hint"))]
    #[inline]
    pub const fn value(self) -> T {
        self.value
    }

    /// Initializes a new value without checking the bounds
    ///
    /// # Safety
    /// Must only be called with a value less than or equal to [Self::MAX](Self::MAX) value.
    #[inline]
    pub const unsafe fn new_unchecked(value: T) -> Self {
        Self { value }
    }
}

impl<T, const BITS: usize> UInt<T, BITS>
where
    Self: Integer,
    T: Copy,
{
    pub const MASK: T = Self::MAX.value;
}

// Next are specific implementations for u8, u16, u32, u64 and u128. A couple notes:
// - The existence of MAX also serves as a neat bounds-check for BITS: If BITS is too large,
//   the subtraction overflows which will fail to compile. This simplifies things a lot.
//   However, that only works if every constructor also uses MAX somehow (doing let _ = MAX is enough)

macro_rules! uint_impl_num {
    // `$const_keyword` is marked as an optional fragment here so that it can conditionally be put on the impl.
    // This macro will be invoked with `u8 as const, ...` if `const_convert_and_const_trait_impl` is enabled.
    ($($type:ident $(as $const_keyword:ident)?),+) => {
        $(
            #[allow(deprecated)]
            impl<const BITS: usize> super::Number for UInt<$type, BITS> {
                type UnderlyingType = $type;
            }

            impl<const BITS: usize> $($const_keyword)? UnsignedInteger for UInt<$type, BITS> {

            }

            impl<const BITS: usize> $($const_keyword)? Integer for UInt<$type, BITS> {
                type UnderlyingType = $type;

                const BITS: usize = BITS;

                const MIN: Self = Self { value: 0 };

                // The existence of MAX also serves as a bounds check: If NUM_BITS is > available bits,
                // we will get a compiler error right here
                const MAX: Self = Self { value: (<$type as Integer>::MAX >> (<$type as Integer>::BITS - Self::BITS)) };

                #[inline]
                fn try_new(value: Self::UnderlyingType) -> Result<Self, TryNewError> {
                    if value <= Self::MAX.value {
                        Ok(Self { value })
                    } else {
                        Err(TryNewError{})
                    }
                }

                #[inline]
                fn new(value: $type) -> Self {
                    assert!(value <= Self::MAX.value);

                    Self { value }
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                #[inline]
                fn from_<T: Integer>(value: T) -> Self {
                    if Self::BITS < T::BITS {
                        assert!(value <= Self::MAX.value.as_());
                    }
                    Self { value: Self::UnderlyingType::masked_new(value) }
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                fn masked_new<T: Integer>(value: T) -> Self {
                    if Self::BITS < T::BITS {
                        Self { value: Self::UnderlyingType::masked_new(value.as_::<Self::UnderlyingType>() & Self::MASK) }
                    } else {
                        Self { value: Self::UnderlyingType::masked_new(value) }
                    }
                }

                fn as_u8(&self) -> u8 {
                    self.value() as _
                }

                fn as_u16(&self) -> u16 {
                    self.value() as _
                }

                fn as_u32(&self) -> u32 {
                    self.value() as _
                }

                fn as_u64(&self) -> u64 {
                    self.value() as _
                }

                fn as_u128(&self) -> u128 {
                    self.value() as _
                }

                fn as_usize(&self) -> usize {
                    self.value() as _
                }

                fn as_i8(&self) -> i8 {
                    self.value() as _
                }

                fn as_i16(&self) -> i16 {
                    self.value() as _
                }

                fn as_i32(&self) -> i32 {
                    self.value() as _
                }

                fn as_i64(&self) -> i64 {
                    self.value() as _
                }

                fn as_i128(&self) -> i128 {
                    self.value() as _
                }

                fn as_isize(&self) -> isize {
                    self.value() as _
                }

                #[inline]
                fn value(self) -> $type {
                    #[cfg(feature = "hint")]
                    unsafe {
                        core::hint::assert_unchecked(self.value <= Self::MAX.value);
                    }

                    self.value
                }
            }
        )+
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
uint_impl_num!(u8, u16, u32, u64, u128);

#[cfg(feature = "const_convert_and_const_trait_impl")]
uint_impl_num!(u8 as const, u16 as const, u32 as const, u64 as const, u128 as const);

macro_rules! uint_impl {
    ($(($type:ident, doctest = $doctest_attr:literal)),+) => {
        $(
            impl<const BITS: usize> UInt<$type, BITS> {
                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn new(value: $type) -> Self {
                    assert!(value <= Self::MAX.value);

                    Self { value }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_u8(value: u8) -> Self {
                    if Self::BITS < 8 {
                        assert!(value <= Self::MAX.value as u8);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_u16(value: u16) -> Self {
                    if Self::BITS < 16 {
                        assert!(value <= Self::MAX.value as u16);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_u32(value: u32) -> Self {
                    if Self::BITS < 32 {
                        assert!(value <= Self::MAX.value as u32);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_u64(value: u64) -> Self {
                    if Self::BITS < 64 {
                        assert!(value <= Self::MAX.value as u64);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_u128(value: u128) -> Self {
                    if Self::BITS < 128 {
                        assert!(value <= Self::MAX.value as u128);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance or an error if the given value is outside of the valid range
                #[inline]
                pub const fn try_new(value: $type) -> Result<Self, TryNewError> {
                    if value <= Self::MAX.value {
                        Ok(Self { value })
                    } else {
                        Err(TryNewError {})
                    }
                }

                /// Returns the type as a fundamental data type
                #[cfg(feature = "hint")]
                #[inline]
                pub const fn value(self) -> $type {
                    // The hint feature requires the type to be const-comparable,
                    // which isn't possible in the generic version above. So we have
                    // an entirely different function if this feature is enabled.
                    // It only works for primitive types, which should be ok in practice
                    // (but is technically an API change)
                    unsafe {
                        core::hint::assert_unchecked(self.value <= Self::MAX.value);
                    }
                    self.value
                }

                #[deprecated(note = "Use one of the specific functions like extract_u32")]
                pub const fn extract(value: $type, start_bit: usize) -> Self {
                    assert!(start_bit + BITS <= $type::BITS as usize);
                    // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                    let _ = Self::MAX;

                    Self {
                        value: (value >> start_bit) & Self::MAX.value,
                    }
                }

                // Generate the `extract_{i,u}{8,16,32,64,128}` functions.
                impl_extract!(
                    $type,
                    "new((value >> start_bit) & MASK)",
                    |value| value & Self::MASK,

                    (8, (u8, extract_u8), (i8, extract_i8)),
                    (16, (u16, extract_u16), (i16, extract_i16)),
                    (32, (u32, extract_u32), (i32, extract_i32)),
                    (64, (u64, extract_u64), (i64, extract_i64)),
                    (128, (u128, extract_u128), (i128, extract_i128))
                );

                /// Returns a [`UInt`] with a wider bit depth but with the same base data type
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn widen<const BITS_RESULT: usize>(
                    self,
                ) -> UInt<$type, BITS_RESULT> {
                    const { if BITS >= BITS_RESULT {
                        panic!("Can not call widen() with the given bit widths");
                    } };

                    // Query MAX of the result to ensure we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                    let _ = UInt::<$type, BITS_RESULT>::MAX;
                    UInt::<$type, BITS_RESULT> { value: self.value }
                }

                /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(200).wrapping_add(u14::new(55)), u14::new(255));
                /// assert_eq!(u14::new(200).wrapping_add(u14::MAX), u14::new(199));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_add(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_add(rhs.value);
                    Self {
                        value: sum & Self::MASK,
                    }
                }

                /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(100).wrapping_sub(u14::new(100)), u14::new(0));
                /// assert_eq!(u14::new(100).wrapping_sub(u14::MAX), u14::new(101));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_sub(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_sub(rhs.value);
                    Self {
                        value: sum & Self::MASK,
                    }
                }

                /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u7;
                /// assert_eq!(u7::new(10).wrapping_mul(u7::new(12)), u7::new(120));
                /// assert_eq!(u7::new(25).wrapping_mul(u7::new(12)), u7::new(44));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_mul(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_mul(rhs.value);
                    Self {
                        value: sum & Self::MASK,
                    }
                }

                /// Wrapping (modular) division. Computes `self / rhs`.
                ///
                /// Wrapped division on unsigned types is just normal division. There’s no way
                /// wrapping could ever happen. This function exists so that all operations are
                /// accounted for in the wrapping operations.
                ///
                /// # Panics
                ///
                /// This function will panic if `rhs` is zero.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(100).wrapping_div(u14::new(10)), u14::new(10));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_div(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_div(rhs.value);
                    Self {
                        // No need to mask here - divisions always produce a result that is <= self
                        value: sum,
                    }
                }

                /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where mask
                /// removes any high-order bits of `rhs` that would cause the shift to
                /// exceed the bitwidth of the type.
                ///
                /// Note that this is not the same as a rotate-left; the RHS of a wrapping
                /// shift-left is restricted to the range of the type, rather than the bits
                /// shifted out of the LHS being returned to the other end.
                /// A [`rotate_left`](Self::rotate_left) function exists as well, which may
                /// be what you want instead.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(1).wrapping_shl(7), u14::new(128));
                /// assert_eq!(u14::new(1).wrapping_shl(128), u14::new(4));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_shl(self, rhs: u32) -> Self {
                    // modulo is expensive on some platforms, so only do it when necessary
                    let shift_amount = if rhs >= (BITS as u32) {
                        rhs % (BITS as u32)
                    } else {
                        rhs
                    };

                    Self {
                        // We could use wrapping_shl here to make Debug builds slightly smaller;
                        // the downside would be that on weird CPUs that don't do wrapping_shl by
                        // default release builds would get slightly worse. Using << should give
                        // good release performance everywere
                        value: (self.value << shift_amount) & Self::MASK,
                    }
                }

                /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where mask removes any
                /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
                ///
                /// Note that this is not the same as a rotate-right; the RHS of a wrapping shift-right is
                /// restricted to the range of the type, rather than the bits shifted out of the LHS being
                /// returned to the other end.
                /// A [`rotate_right`](Self::rotate_right) function exists as well, which may be what you
                /// want instead.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(128).wrapping_shr(7), u14::new(1));
                /// assert_eq!(u14::new(128).wrapping_shr(128), u14::new(32));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_shr(self, rhs: u32) -> Self {
                    // modulo is expensive on some platforms, so only do it when necessary
                    let shift_amount = if rhs >= (BITS as u32) {
                        rhs % (BITS as u32)
                    } else {
                        rhs
                    };

                    Self {
                        value: (self.value >> shift_amount),
                    }
                }

                /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(100).saturating_add(u14::new(1)), u14::new(101));
                /// assert_eq!(u14::MAX.saturating_add(u14::new(100)), u14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_add(self, rhs: Self) -> Self {
                    let saturated = if Self::UNUSED_BITS == 0 {
                        // We are something like a UInt::<u8; 8>, we can fallback to the base implementation.
                        // This is very unlikely to happen in practice, but checking allows us to use
                        // `wrapping_add` instead of `saturating_add` in the common case, which is faster.
                        self.value.saturating_add(rhs.value)
                    } else {
                        // We're dealing with fewer bits than the underlying type (e.g. u7).
                        // That means the addition can never overflow the underlying type
                        let sum = self.value.wrapping_add(rhs.value);
                        let max = Self::MAX.value();
                        if sum > max { max } else { sum }
                    };
                    Self {
                        value: saturated,
                    }
                }

                /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(100).saturating_sub(u14::new(27)), u14::new(73));
                /// assert_eq!(u14::new(13).saturating_sub(u14::new(127)), u14::new(0));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_sub(self, rhs: Self) -> Self {
                    // For unsigned numbers, the only difference is when we reach 0 - which is the same
                    // no matter the data size
                    Self {
                        value: self.value.saturating_sub(rhs.value),
                    }
                }

                /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(2).saturating_mul(u14::new(10)), u14::new(20));
                /// assert_eq!(u14::MAX.saturating_mul(u14::new(10)), u14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_mul(self, rhs: Self) -> Self {
                    let product = if (BITS << 1) <= (core::mem::size_of::<$type>() << 3) {
                        // We have half the bits (e.g. u4 * u4) of the base type, so we can't overflow the base type
                        // wrapping_mul likely provides the best performance on all cpus
                        self.value.wrapping_mul(rhs.value)
                    } else {
                        // We have more than half the bits (e.g. u6 * u6)
                        self.value.saturating_mul(rhs.value)
                    };

                    let max = Self::MAX.value();
                    let saturated = if product > max { max } else { product };
                    Self {
                        value: saturated,
                    }
                }

                /// Saturating integer division. Computes `self / rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Panics
                ///
                /// This function will panic if rhs is zero.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(5).saturating_div(u14::new(2)), u14::new(2));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_div(self, rhs: Self) -> Self {
                    // When dividing unsigned numbers, we never need to saturate.
                    // Division by zero in saturating_div throws an exception (in debug and release mode),
                    // so no need to do anything special there either
                    Self {
                        value: self.value.saturating_div(rhs.value),
                    }
                }

                /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(4).saturating_pow(3), u14::new(64));
                /// assert_eq!(u14::MAX.saturating_pow(2), u14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_pow(self, exp: u32) -> Self {
                    // It might be possible to handwrite this to be slightly faster as both
                    // `saturating_pow` has to do a bounds-check and then we do second one.
                    let powed = self.value.saturating_pow(exp);
                    let max = Self::MAX.value();
                    let saturated = if powed > max { max } else { powed };
                    Self {
                        value: saturated,
                    }
                }

                /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!((u14::MAX - u14::new(2)).checked_add(u14::new(1)), Some(u14::MAX - u14::new(1)));
                /// assert_eq!((u14::MAX - u14::new(2)).checked_add(u14::new(3)), None);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                    if Self::UNUSED_BITS == 0 {
                        // We are something like a UInt::<u8; 8>, we can fallback to the base implementation.
                        // This is very unlikely to happen in practice, but checking allows us to use
                        // `wrapping_add` instead of `checked_add` in the common case, which is faster.
                        match self.value().checked_add(rhs.value()) {
                            Some(value) => Some(Self { value }),
                            None => None
                        }
                    } else {
                        // We're dealing with fewer bits than the underlying type (e.g. u7).
                        // That means the addition can never overflow the underlying type
                        let sum = self.value().wrapping_add(rhs.value());
                        if sum > Self::MAX.value() { None } else { Some(Self { value: sum })}
                    }
                }

                /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(1).checked_sub(u14::new(1)), Some(u14::new(0)));
                /// assert_eq!(u14::new(0).checked_sub(u14::new(1)), None);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
                    match self.value().checked_sub(rhs.value()) {
                        Some(value) => Some(Self { value }),
                        None => None
                    }
                }

                /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occurred.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u14::new(5).checked_mul(u14::new(1)), Some(u14::new(5)));
                /// assert_eq!(u14::MAX.checked_mul(u14::new(2)), None);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
                    let product = if (BITS << 1) <= (core::mem::size_of::<$type>() << 3) {
                        // We have half the bits (e.g. `u4 * u4`) of the base type, so we can't overflow the base type.
                        // `wrapping_mul` likely provides the best performance on all CPUs.
                        Some(self.value().wrapping_mul(rhs.value()))
                    } else {
                        // We have more than half the bits (e.g. u6 * u6)
                        self.value().checked_mul(rhs.value())
                    };

                    match product {
                        Some(value) if value <= Self::MAX.value() => Some(Self { value }),
                        _ => None
                    }
                }

                /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(128).checked_div(u14::new(2)), Some(u14::new(64)));
                /// assert_eq!(u14::new(1).checked_div(u14::new(0)), None);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_div(self, rhs: Self) -> Option<Self> {
                    match self.value().checked_div(rhs.value()) {
                        Some(value) => Some(Self { value }),
                        None => None
                    }
                }

                /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is larger than
                /// or equal to the number of bits in `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(0x1).checked_shl(4), Some(u14::new(0x10)));
                /// assert_eq!(u14::new(0x10).checked_shl(129), None);
                /// assert_eq!(u14::new(0x10).checked_shl(13), Some(u14::new(0)));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
                    if rhs >= (BITS as u32) {
                        None
                    } else {
                        Some(Self {
                            value: (self.value() << rhs) & Self::MASK,
                        })
                    }
                }

                /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs` is larger than
                /// or equal to the number of bits in `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::u14;
                /// assert_eq!(u14::new(0x10).checked_shr(4), Some(u14::new(0x1)));
                /// assert_eq!(u14::new(0x10).checked_shr(129), None);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
                    if rhs >= (BITS as u32) {
                        None
                    } else {
                        Some(Self {
                            value: self.value() >> rhs,
                        })
                    }
                }

                pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                    let (value, overflow) = if Self::UNUSED_BITS == 0 {
                        // We are something like a UInt::<u8; 8>. We can fallback to the base implementation
                        self.value.overflowing_add(rhs.value)
                    } else {
                        // We're dealing with fewer bits than the underlying type (e.g. u7).
                        // That means the addition can never overflow the underlying type
                        let sum = self.value.wrapping_add(rhs.value);
                        let masked = sum & Self::MASK;
                        (masked, masked != sum)
                    };
                    (Self { value }, overflow)
                }

                pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                    // For unsigned numbers, the only difference is when we reach 0 - which is the same
                    // no matter the data size. In the case of overflow we do have the mask the result though
                    let (value, overflow) = self.value.overflowing_sub(rhs.value);
                    (Self { value: value & Self::MASK }, overflow)
                }

                pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                    let (wrapping_product, overflow) = if (BITS << 1) <= (core::mem::size_of::<$type>() << 3) {
                        // We have half the bits (e.g. u4 * u4) of the base type, so we can't overflow the base type
                        // wrapping_mul likely provides the best performance on all cpus
                        self.value.overflowing_mul(rhs.value)
                    } else {
                        // We have more than half the bits (e.g. u6 * u6)
                        self.value.overflowing_mul(rhs.value)
                    };

                    let masked = wrapping_product & Self::MASK;
                    let overflow2 = masked != wrapping_product;
                    (Self { value: masked }, overflow || overflow2 )
                }

                pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
                    let value = self.value.wrapping_div(rhs.value);
                    (Self { value }, false )
                }

                pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
                    if rhs >= (BITS as u32) {
                        (Self { value: self.value << (rhs % (BITS as u32)) }, true)
                    } else {
                        (Self { value: self.value << rhs }, false)
                    }
                }

                pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
                    if rhs >= (BITS as u32) {
                        (Self { value: self.value >> (rhs % (BITS as u32)) }, true)
                    } else {
                        (Self { value: self.value >> rhs }, false)
                    }
                }

                /// Reverses the order of bits in the integer. The least significant bit becomes the most
                /// significant bit, second least-significant bit becomes second most-significant bit, etc.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// assert_eq!(u6::new(0b10_1010).reverse_bits(), u6::new(0b01_0101));
                /// assert_eq!(u6::new(0), u6::new(0).reverse_bits());
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn reverse_bits(self) -> Self {
                    Self { value: self.value().reverse_bits() >> Self::UNUSED_BITS }
                }

                /// Returns the number of ones in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u7::new(0b100_1100);
                /// assert_eq!(n.count_ones(), 3);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.count_ones(), 7);
                ///
                /// let zero = u7::new(0);
                /// assert_eq!(zero.count_ones(), 0);
                /// ```
                #[inline]
                pub const fn count_ones(self) -> u32 {
                    // The upper bits are zero, so we can ignore them
                    self.value().count_ones()
                }

                /// Returns the number of zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let zero = u7::new(0);
                /// assert_eq!(zero.count_zeros(), 7);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.count_zeros(), 0);
                /// ```
                #[inline]
                pub const fn count_zeros(self) -> u32 {
                    // The upper bits are zero, so we can have to subtract them from the result.
                    // We can avoid a bounds check in debug builds with `wrapping_sub` since this cannot overflow.
                    self.value().count_zeros().wrapping_sub(Self::UNUSED_BITS as u32)
                }

                /// Returns the number of leading ones in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = !(u7::MAX >> 2);
                /// assert_eq!(n.leading_ones(), 2);
                ///
                /// let zero = u7::new(0);
                /// assert_eq!(zero.leading_ones(), 0);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.leading_ones(), 7);
                /// ```
                #[inline]
                pub const fn leading_ones(self) -> u32 {
                    (self.value() << Self::UNUSED_BITS).leading_ones()
                }

                /// Returns the number of leading zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u7::MAX >> 2;
                /// assert_eq!(n.leading_zeros(), 2);
                ///
                /// let zero = u7::new(0);
                /// assert_eq!(zero.leading_zeros(), 7);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.leading_zeros(), 0);
                /// ```
                #[inline]
                pub const fn leading_zeros(self) -> u32 {
                    if Self::UNUSED_BITS == 0 {
                        self.value().leading_zeros()
                    } else {
                        // Prevent an all-zero value reporting the underlying type's entire bit width by setting
                        // the first unused bit to one, causing `leading_zeros()` to ignore the unused bits.
                        let first_unused_bit_set = const { 1 << (Self::UNUSED_BITS - 1) };
                        ((self.value() << Self::UNUSED_BITS) | first_unused_bit_set).leading_zeros()
                    }
                }

                /// Returns the number of trailing ones in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u7::new(0b1010111);
                /// assert_eq!(n.trailing_ones(), 3);
                ///
                /// let zero = u7::new(0);
                /// assert_eq!(zero.trailing_ones(), 0);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.trailing_ones(), 7);
                /// ```
                #[inline]
                pub const fn trailing_ones(self) -> u32 {
                    self.value().trailing_ones()
                }

                /// Returns the number of trailing zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u7::new(0b010_1000);
                /// assert_eq!(n.trailing_zeros(), 3);
                ///
                /// let zero = u7::new(0);
                /// assert_eq!(zero.trailing_zeros(), 7);
                ///
                /// let max = u7::MAX;
                /// assert_eq!(max.trailing_zeros(), 0);
                /// ```
                #[inline]
                pub const fn trailing_zeros(self) -> u32 {
                    // Prevent an all-zeros value reporting the underlying type's entire bit width by setting
                    // all the unused bits.
                    (self.value() | !Self::MASK).trailing_zeros()
                }

                /// Shifts the bits to the left by a specified amount, `n`, wrapping the truncated bits
                /// to the end of the resulting integer.
                ///
                /// Please note this isn’t the same operation as the `<<` shifting operator!
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u6::new(0b10_1010);
                /// let m = u6::new(0b01_0101);
                ///
                /// assert_eq!(n.rotate_left(1), m);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn rotate_left(self, n: u32) -> Self {
                    let b = BITS as u32;
                    let n = if n >= b { n % b } else { n };

                    let moved_bits = (self.value() << n) & Self::MASK;
                    let truncated_bits = self.value() >> (b - n);
                    Self { value: moved_bits | truncated_bits }
                }

                /// Shifts the bits to the right by a specified amount, `n`, wrapping the truncated bits
                /// to the beginning of the resulting integer.
                ///
                /// Please note this isn’t the same operation as the `>>` shifting operator!
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                #[doc = concat!(" ```", $doctest_attr)]
                /// # use arbitrary_int::prelude::*;
                /// let n = u6::new(0b10_1010);
                /// let m = u6::new(0b01_0101);
                ///
                /// assert_eq!(n.rotate_right(1), m);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn rotate_right(self, n: u32) -> Self {
                    let b = BITS as u32;
                    let n = if n >= b { n % b } else { n };

                    let moved_bits = self.value() >> n;
                    let truncated_bits = (self.value() << (b - n)) & Self::MASK;
                    Self { value: moved_bits | truncated_bits }
                }
            }
        )+
    };
}

// Because the methods within this macro are effectively copy-pasted for each underlying integer type,
// each documentation test gets executed five times (once for each underlying type), even though the
// tests themselves aren't specific to said underlying type. This severely slows down `cargo test`,
// so we ignore them for all but one (arbitrary) underlying type.
uint_impl!(
    (u8, doctest = "rust"),
    (u16, doctest = "ignore"),
    (u32, doctest = "ignore"),
    (u64, doctest = "ignore"),
    (u128, doctest = "ignore")
);

// Arithmetic implementations
impl<T, const BITS: usize> Add for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq
        + Copy
        + BitAnd<T, Output = T>
        + Not<Output = T>
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value + rhs.value;
        #[cfg(debug_assertions)]
        if (sum & !Self::MASK) != T::from(0) {
            panic!("attempt to add with overflow");
        }
        Self {
            value: sum & Self::MASK,
        }
    }
}

impl<T, const BITS: usize> AddAssign for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq
        + Eq
        + Not<Output = T>
        + Copy
        + AddAssign<T>
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + From<u8>,
{
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        #[cfg(debug_assertions)]
        if (self.value & !Self::MASK) != T::from(0) {
            panic!("attempt to add with overflow");
        }
        self.value &= Self::MASK;
    }
}

impl<T, const BITS: usize> Sub for UInt<T, BITS>
where
    Self: Integer,
    T: Copy + BitAnd<T, Output = T> + Sub<T, Output = T>,
{
    type Output = UInt<T, BITS>;

    fn sub(self, rhs: Self) -> Self::Output {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        Self {
            value: (self.value - rhs.value) & Self::MASK,
        }
    }
}

impl<T, const BITS: usize> SubAssign for UInt<T, BITS>
where
    Self: Integer,
    T: Copy + SubAssign<T> + BitAnd<T, Output = T> + BitAndAssign<T> + Sub<T, Output = T>,
{
    fn sub_assign(&mut self, rhs: Self) {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        self.value -= rhs.value;
        self.value &= Self::MASK;
    }
}

impl<T, const BITS: usize> Mul for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq + Copy + BitAnd<T, Output = T> + Not<Output = T> + Mul<T, Output = T> + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn mul(self, rhs: Self) -> Self::Output {
        // In debug builds, this will perform two bounds checks: Initial multiplication, followed by
        // our bounds check. As wrapping_mul isn't available as a trait bound (in regular Rust), this
        // is unavoidable
        let product = self.value * rhs.value;
        #[cfg(debug_assertions)]
        if (product & !Self::MASK) != T::from(0) {
            panic!("attempt to multiply with overflow");
        }
        Self {
            value: product & Self::MASK,
        }
    }
}

impl<T, const BITS: usize> MulAssign for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq
        + Eq
        + Not<Output = T>
        + Copy
        + MulAssign<T>
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + From<u8>,
{
    fn mul_assign(&mut self, rhs: Self) {
        self.value *= rhs.value;
        #[cfg(debug_assertions)]
        if (self.value & !Self::MASK) != T::from(0) {
            panic!("attempt to multiply with overflow");
        }
        self.value &= Self::MASK;
    }
}

impl<T, const BITS: usize> Div for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq + Div<T, Output = T>,
{
    type Output = UInt<T, BITS>;

    fn div(self, rhs: Self) -> Self::Output {
        // Integer division can only make the value smaller. And as the result is same type as
        // Self, there's no need to range-check or mask
        Self {
            value: self.value / rhs.value,
        }
    }
}

impl<T, const BITS: usize> DivAssign for UInt<T, BITS>
where
    Self: Integer,
    T: PartialEq + DivAssign<T>,
{
    fn div_assign(&mut self, rhs: Self) {
        self.value /= rhs.value;
    }
}

impl<T, const BITS: usize> BitAnd for UInt<T, BITS>
where
    Self: Integer,
    T: Copy
        + BitAnd<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value & rhs.value,
        }
    }
}

impl<T, const BITS: usize> BitAndAssign for UInt<T, BITS>
where
    T: Copy + BitAndAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitand_assign(&mut self, rhs: Self) {
        self.value &= rhs.value;
    }
}

impl<T, const BITS: usize> BitOr for UInt<T, BITS>
where
    T: Copy + BitOr<T, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value | rhs.value,
        }
    }
}

impl<T, const BITS: usize> BitOrAssign for UInt<T, BITS>
where
    T: Copy + BitOrAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitor_assign(&mut self, rhs: Self) {
        self.value |= rhs.value;
    }
}

impl<T, const BITS: usize> BitXor for UInt<T, BITS>
where
    T: Copy + BitXor<T, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value ^ rhs.value,
        }
    }
}

impl<T, const BITS: usize> BitXorAssign for UInt<T, BITS>
where
    T: Copy + BitXorAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitxor_assign(&mut self, rhs: Self) {
        self.value ^= rhs.value;
    }
}

impl<T, const BITS: usize> Not for UInt<T, BITS>
where
    Self: Integer,
    T: Copy
        + BitAnd<T, Output = T>
        + BitXor<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, BITS>;

    fn not(self) -> Self::Output {
        Self {
            value: self.value ^ Self::MASK,
        }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> Shl<TSHIFTBITS> for UInt<T, BITS>
where
    Self: Integer,
    T: Copy
        + BitAnd<T, Output = T>
        + Shl<TSHIFTBITS, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    type Output = UInt<T, BITS>;

    fn shl(self, rhs: TSHIFTBITS) -> Self::Output {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        #[cfg(debug_assertions)]
        if rhs.try_into().unwrap_or(usize::MAX) >= BITS {
            panic!("attempt to shift left with overflow")
        }

        Self {
            value: (self.value << rhs) & Self::MASK,
        }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> ShlAssign<TSHIFTBITS> for UInt<T, BITS>
where
    Self: Integer,
    T: Copy
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + ShlAssign<TSHIFTBITS>
        + Sub<T, Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    fn shl_assign(&mut self, rhs: TSHIFTBITS) {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        #[cfg(debug_assertions)]
        if rhs.try_into().unwrap_or(usize::MAX) >= BITS {
            panic!("attempt to shift left with overflow")
        }
        self.value <<= rhs;
        self.value &= Self::MASK;
    }
}

impl<T, TSHIFTBITS, const BITS: usize> Shr<TSHIFTBITS> for UInt<T, BITS>
where
    T: Copy + Shr<TSHIFTBITS, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    type Output = UInt<T, BITS>;

    fn shr(self, rhs: TSHIFTBITS) -> Self::Output {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        #[cfg(debug_assertions)]
        if rhs.try_into().unwrap_or(usize::MAX) >= BITS {
            panic!("attempt to shift left with overflow")
        }
        Self {
            value: self.value >> rhs,
        }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> ShrAssign<TSHIFTBITS> for UInt<T, BITS>
where
    T: Copy + ShrAssign<TSHIFTBITS> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    fn shr_assign(&mut self, rhs: TSHIFTBITS) {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        #[cfg(debug_assertions)]
        if rhs.try_into().unwrap_or(usize::MAX) >= BITS {
            panic!("attempt to shift left with overflow")
        }
        self.value >>= rhs;
    }
}

impl<T, const BITS: usize> Display for UInt<T, BITS>
where
    T: Display,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> Debug for UInt<T, BITS>
where
    T: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> LowerHex for UInt<T, BITS>
where
    T: LowerHex,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> UpperHex for UInt<T, BITS>
where
    T: UpperHex,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> Octal for UInt<T, BITS>
where
    T: Octal,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> Binary for UInt<T, BITS>
where
    T: Binary,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

#[cfg(feature = "defmt")]
impl<T, const BITS: usize> defmt::Format for UInt<T, BITS>
where
    T: defmt::Format,
{
    #[inline]
    fn format(&self, f: defmt::Formatter) {
        self.value.format(f)
    }
}

#[cfg(feature = "borsh")]
impl<T, const BITS: usize> borsh::BorshSerialize for UInt<T, BITS>
where
    Self: Integer,
    T: borsh::BorshSerialize,
{
    fn serialize<W: borsh::io::Write>(&self, writer: &mut W) -> borsh::io::Result<()> {
        let serialized_byte_count = (BITS + 7) / 8;
        let mut buffer = [0u8; 16];
        self.value.serialize(&mut &mut buffer[..])?;
        writer.write(&buffer[0..serialized_byte_count])?;

        Ok(())
    }
}

#[cfg(feature = "borsh")]
impl<
        T: borsh::BorshDeserialize + PartialOrd<<UInt<T, BITS> as Integer>::UnderlyingType>,
        const BITS: usize,
    > borsh::BorshDeserialize for UInt<T, BITS>
where
    Self: Integer,
{
    fn deserialize_reader<R: borsh::io::Read>(reader: &mut R) -> borsh::io::Result<Self> {
        // Ideally, we'd want a buffer of size `BITS >> 3` or `size_of::<T>`, but that's not possible
        // with arrays at present (feature(generic_const_exprs), once stable, will allow this).
        // vec! would be an option, but an allocation is not expected at this level.
        // Therefore, allocate a 16 byte buffer and take a slice out of it.
        let serialized_byte_count = (BITS + 7) / 8;
        let underlying_byte_count = core::mem::size_of::<T>();
        let mut buf = [0u8; 16];

        // Read from the source, advancing cursor by the exact right number of bytes
        reader.read(&mut buf[..serialized_byte_count])?;

        // Deserialize the underlying type. We have to pass in the correct number of bytes of the
        // underlying type (or more, but let's be precise). The unused bytes are all still zero
        let value = T::deserialize(&mut &buf[..underlying_byte_count])?;

        if value >= Self::MIN.value() && value <= Self::MAX.value() {
            Ok(Self { value })
        } else {
            Err(borsh::io::Error::new(
                borsh::io::ErrorKind::InvalidData,
                "Value out of range",
            ))
        }
    }
}

#[cfg(feature = "borsh")]
impl<T, const BITS: usize> borsh::BorshSchema for UInt<T, BITS> {
    fn add_definitions_recursively(
        definitions: &mut BTreeMap<borsh::schema::Declaration, borsh::schema::Definition>,
    ) {
        definitions.insert(
            ["u", &BITS.to_string()].concat(),
            borsh::schema::Definition::Primitive(((BITS + 7) / 8) as u8),
        );
    }

    fn declaration() -> borsh::schema::Declaration {
        ["u", &BITS.to_string()].concat()
    }
}

#[cfg(feature = "serde")]
impl<T, const BITS: usize> Serialize for UInt<T, BITS>
where
    T: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.value.serialize(serializer)
    }
}

// Serde's invalid_value error (https://rust-lang.github.io/hashbrown/serde/de/trait.Error.html#method.invalid_value)
// takes an Unexpected (https://rust-lang.github.io/hashbrown/serde/de/enum.Unexpected.html) which only accepts a 64 bit
// unsigned integer. This is a problem for us because we want to support 128 bit unsigned integers. To work around this
// we define our own error type using the UInt's underlying type which implements Display and then use
// serde::de::Error::custom to create an error with our custom type.
#[cfg(feature = "serde")]
struct InvalidUIntValueError<T>
where
    T: Integer,
    T::UnderlyingType: Display,
{
    value: T::UnderlyingType,
}

#[cfg(feature = "serde")]
impl<T> Display for InvalidUIntValueError<T>
where
    T: Integer,
    T::UnderlyingType: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "invalid value: integer `{}`, expected a value between `0` and `{}`",
            self.value,
            T::MAX.value()
        )
    }
}

#[cfg(feature = "serde")]
impl<'de, T, const BITS: usize> Deserialize<'de> for UInt<T, BITS>
where
    Self: Integer<UnderlyingType = T>,
    T: Display + PartialOrd + Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = T::deserialize(deserializer)?;

        if value <= Self::MAX.value {
            Ok(Self { value })
        } else {
            let err = InvalidUIntValueError::<Self> { value };
            Err(serde::de::Error::custom(err))
        }
    }
}

#[cfg(feature = "schemars")]
impl<T, const BITS: usize> JsonSchema for UInt<T, BITS>
where
    Self: Integer,
{
    fn schema_name() -> String {
        ["uint", &BITS.to_string()].concat()
    }

    fn json_schema(_gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        use schemars::schema::{NumberValidation, Schema, SchemaObject};
        let schema_object = SchemaObject {
            instance_type: Some(schemars::schema::InstanceType::Integer.into()),
            format: Some(Self::schema_name()),
            number: Some(Box::new(NumberValidation {
                // can be done with https://github.com/rust-lang/rfcs/pull/2484
                // minimum: Some(Self::MIN.value().try_into().ok().unwrap()),
                // maximum: Some(Self::MAX.value().try_into().ok().unwrap()),
                ..Default::default()
            })),
            ..Default::default()
        };
        Schema::Object(schema_object)
    }
}

#[cfg(feature = "step_trait")]
impl<T, const BITS: usize> Step for UInt<T, BITS>
where
    Self: Integer<UnderlyingType = T>,
    T: Copy + Step,
{
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
        Step::steps_between(&start.value(), &end.value())
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        if let Some(res) = Step::forward_checked(start.value(), count) {
            Self::try_new(res).ok()
        } else {
            None
        }
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        if let Some(res) = Step::backward_checked(start.value(), count) {
            Self::try_new(res).ok()
        } else {
            None
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T, const NUM_BITS: usize> num_traits::WrappingAdd for UInt<T, NUM_BITS>
where
    Self: Integer,
    T: PartialEq
        + Eq
        + Copy
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + BitAnd<T, Output = T>
        + Not<Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
    Wrapping<T>: Add<Wrapping<T>, Output = Wrapping<T>>,
{
    #[inline]
    fn wrapping_add(&self, rhs: &Self) -> Self {
        let sum = (Wrapping(self.value) + Wrapping(rhs.value)).0;
        Self {
            value: sum & Self::MASK,
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T, const NUM_BITS: usize> num_traits::WrappingSub for UInt<T, NUM_BITS>
where
    Self: Integer,
    T: PartialEq
        + Eq
        + Copy
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + BitAnd<T, Output = T>
        + Not<Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
    Wrapping<T>: Sub<Wrapping<T>, Output = Wrapping<T>>,
{
    #[inline]
    fn wrapping_sub(&self, rhs: &Self) -> Self {
        let sum = (Wrapping(self.value) - Wrapping(rhs.value)).0;
        Self {
            value: sum & Self::MASK,
        }
    }
}

#[cfg(feature = "num-traits")]
impl<T, const NUM_BITS: usize> num_traits::bounds::Bounded for UInt<T, NUM_BITS>
where
    Self: Integer,
{
    fn min_value() -> Self {
        Self::MIN
    }

    fn max_value() -> Self {
        Self::MAX
    }
}

bytes_operation_impl!(UInt<u32, 24>, u32);
bytes_operation_impl!(UInt<u64, 24>, u64);
bytes_operation_impl!(UInt<u128, 24>, u128);
bytes_operation_impl!(UInt<u64, 40>, u64);
bytes_operation_impl!(UInt<u128, 40>, u128);
bytes_operation_impl!(UInt<u64, 48>, u64);
bytes_operation_impl!(UInt<u128, 48>, u128);
bytes_operation_impl!(UInt<u64, 56>, u64);
bytes_operation_impl!(UInt<u128, 56>, u128);
bytes_operation_impl!(UInt<u128, 72>, u128);
bytes_operation_impl!(UInt<u128, 80>, u128);
bytes_operation_impl!(UInt<u128, 88>, u128);
bytes_operation_impl!(UInt<u128, 96>, u128);
bytes_operation_impl!(UInt<u128, 104>, u128);
bytes_operation_impl!(UInt<u128, 112>, u128);
bytes_operation_impl!(UInt<u128, 120>, u128);

// Conversions
from_arbitrary_int_impl!(UInt(u8), [u16, u32, u64, u128]);
from_arbitrary_int_impl!(UInt(u16), [u8, u32, u64, u128]);
from_arbitrary_int_impl!(UInt(u32), [u8, u16, u64, u128]);
from_arbitrary_int_impl!(UInt(u64), [u8, u16, u32, u128]);
from_arbitrary_int_impl!(UInt(u128), [u8, u32, u64, u16]);

from_native_impl!(UInt(u8), [u8, u16, u32, u64, u128]);
from_native_impl!(UInt(u16), [u8, u16, u32, u64, u128]);
from_native_impl!(UInt(u32), [u8, u16, u32, u64, u128]);
from_native_impl!(UInt(u64), [u8, u16, u32, u64, u128]);
from_native_impl!(UInt(u128), [u8, u16, u32, u64, u128]);

pub use aliases::*;

#[allow(non_camel_case_types)]
#[rustfmt::skip]
pub(crate) mod aliases {
    use crate::common::type_alias;

    type_alias!(UInt(u8), (u1, 1), (u2, 2), (u3, 3), (u4, 4), (u5, 5), (u6, 6), (u7, 7));
    type_alias!(UInt(u16), (u9, 9), (u10, 10), (u11, 11), (u12, 12), (u13, 13), (u14, 14), (u15, 15));
    type_alias!(UInt(u32), (u17, 17), (u18, 18), (u19, 19), (u20, 20), (u21, 21), (u22, 22), (u23, 23), (u24, 24), (u25, 25), (u26, 26), (u27, 27), (u28, 28), (u29, 29), (u30, 30), (u31, 31));
    type_alias!(UInt(u64), (u33, 33), (u34, 34), (u35, 35), (u36, 36), (u37, 37), (u38, 38), (u39, 39), (u40, 40), (u41, 41), (u42, 42), (u43, 43), (u44, 44), (u45, 45), (u46, 46), (u47, 47), (u48, 48), (u49, 49), (u50, 50), (u51, 51), (u52, 52), (u53, 53), (u54, 54), (u55, 55), (u56, 56), (u57, 57), (u58, 58), (u59, 59), (u60, 60), (u61, 61), (u62, 62), (u63, 63));
    type_alias!(UInt(u128), (u65, 65), (u66, 66), (u67, 67), (u68, 68), (u69, 69), (u70, 70), (u71, 71), (u72, 72), (u73, 73), (u74, 74), (u75, 75), (u76, 76), (u77, 77), (u78, 78), (u79, 79), (u80, 80), (u81, 81), (u82, 82), (u83, 83), (u84, 84), (u85, 85), (u86, 86), (u87, 87), (u88, 88), (u89, 89), (u90, 90), (u91, 91), (u92, 92), (u93, 93), (u94, 94), (u95, 95), (u96, 96), (u97, 97), (u98, 98), (u99, 99), (u100, 100), (u101, 101), (u102, 102), (u103, 103), (u104, 104), (u105, 105), (u106, 106), (u107, 107), (u108, 108), (u109, 109), (u110, 110), (u111, 111), (u112, 112), (u113, 113), (u114, 114), (u115, 115), (u116, 116), (u117, 117), (u118, 118), (u119, 119), (u120, 120), (u121, 121), (u122, 122), (u123, 123), (u124, 124), (u125, 125), (u126, 126), (u127, 127));
}

macro_rules! boolu1 {
    ($($const_keyword:ident)?) => {
        impl $($const_keyword)? From<bool> for u1 {
            #[inline]
            fn from(value: bool) -> Self {
                u1::new(value as u8)
            }
        }

        impl $($const_keyword)? From<u1> for bool {
            #[inline]
            fn from(value: u1) -> Self {
                match value.value() {
                    0 => false,
                    1 => true,
                    _ => unreachable!(), // TODO: unreachable!() is not const yet
                }
            }
        }
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
boolu1!();

#[cfg(feature = "const_convert_and_const_trait_impl")]
boolu1!(const);
