use crate::TryNewError;
use core::fmt::Debug;

pub(crate) mod sealed {
    /// Ensures that outside users can not implement the traits provided by this crate.
    #[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
    pub trait Sealed {}
}

// TODO: SignedUnderlyingType for consistency?

/// The base trait for integer numbers, either built-in (u8, i8, u16, i16, u32, i32, u64, i64,
/// u128, i128) or arbitrary-int (u1, i1, u7, i7 etc.).
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait Integer:
    Sized + Copy + Clone + PartialOrd + Ord + PartialEq + Eq + sealed::Sealed
{
    /// The primitive type that is used to represent the value of an [`Int`] or [`UInt`] in memory.
    /// Its bit width must be greater than or equal to [`BITS`](Self::BITS), and it must be signed.
    /// In practice this will one of:
    /// - For [`UInt`]: [`u8`], [`u16`], [`u32`], [`u64`] or [`u128`].
    /// - For [`Int`]: [`i8`], [`i16`], [`i32`], [`i64`] or [`i128`].
    ///
    /// The number of bits used decides which underlying type is used: it uses the smallest possible
    /// primitive that has enough space to store the entire value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// fn uses_u8<T: Integer<UnderlyingType = u8>>(value: T) {}
    /// fn uses_i8<T: Integer<UnderlyingType = i8>>(value: T) {}
    ///
    /// // Ok: u1, u2, ..., u7 all use an u8 as their underlying type.
    /// uses_u8(u3::new(0));
    /// uses_u8(u4::new(1));
    /// uses_u8(u7::MAX);
    ///
    /// // Ok: i1, i2, ..., i7 all use an i8 as their underlying type.
    /// uses_i8(i3::new(0));
    /// uses_i8(i4::new(1));
    /// uses_i8(i7::MAX);
    /// ```
    ///
    /// ```compile_fail
    /// # use arbitrary_int::prelude::*;
    /// fn uses_u8<T: Integer<UnderlyingType = u8>>(value: T) {}
    /// fn uses_i8<T: Integer<UnderlyingType = i8>>(value: T) {}
    ///
    /// // Error: the value of an u9/i9 is too large to fit inside of an u8/i8,
    /// // so its underlying type is rounded up to an u16/i16 instead.
    /// uses_u8(u9::new(0));
    /// uses_i8(i9::new(0));
    ///
    /// // Error: The underlying type's sign always matches the number type.
    /// uses_u8(i3::new(0));
    /// uses_i8(u3::new(0));
    /// ```
    ///
    /// [`UInt`]: crate::UInt
    /// [`Int`]: crate::Int
    type UnderlyingType: Integer
        + Debug
        + TryFrom<u8>
        + TryFrom<u16>
        + TryFrom<u32>
        + TryFrom<u64>
        + TryFrom<u128>;

    /// The unsigned primitive type with a bit width equal to that of [`UnderlyingType`].
    /// This type must be unsigned.
    ///
    /// For unsigned numbers, this is guaranteed to be the same as [`UnderlyingType`].
    /// For signed numbers, this type is one of the following (depending on [`UnderlyingType`]):
    /// - [`u8`], [`u16`], [`u32`], [`u64`] or [`u128`].
    ///
    /// See [`UnderlyingType`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// fn uses_i8<T>(value: T)
    /// where
    ///     T: Integer<UnderlyingType = i8, UnsignedUnderlyingType = u8>,
    /// {}
    ///
    /// fn uses_u8<T>(value: T)
    /// where
    ///     T: Integer<UnderlyingType = u8, UnsignedUnderlyingType = u8>,
    /// {}
    ///
    /// // Ok: i1, i2, ..., i7 all use an i8 as their underlying type, whose unsigned equivalent is u8.
    /// uses_i8(i3::new(0));
    /// uses_u8(u3::new(0));
    /// ```
    ///
    /// [`UnderlyingType`]: Self::UnderlyingType
    type UnsignedUnderlyingType: Integer
        + Debug
        + From<u8>
        + TryFrom<u16>
        + TryFrom<u32>
        + TryFrom<u64>
        + TryFrom<u128>;

    /// The signed primitive type with a bit width equal to that of [`UnderlyingType`].
    /// This type must be signed.
    ///
    /// For signed numbers, this is guaranteed to be the same as [`UnderlyingType`].
    /// For unsigned numbers, this type is one of the following (depending on [`UnderlyingType`]):
    /// - [`i8`], [`i16`], [`i32`], [`i64`] or [`i128`].
    ///
    /// See [`UnderlyingType`] for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// fn uses_i8<T>(value: T)
    /// where
    ///     T: Integer<UnderlyingType = i8, SignedUnderlyingType = i8>,
    /// {}
    ///
    /// fn uses_u8<T>(value: T)
    /// where
    ///     T: Integer<UnderlyingType = u8, SignedUnderlyingType = i8>,
    /// {}
    ///
    /// // Ok: u1, u2, ..., u7 all use an u8 as their underlying type, whose unsigned equivalent is i8.
    /// uses_u8(u3::new(0));
    /// uses_i8(i3::new(0));
    /// ```
    ///
    /// [`UnderlyingType`]: Self::UnderlyingType
    type SignedUnderlyingType: Integer
        + Debug
        + From<i8>
        + TryFrom<i16>
        + TryFrom<i32>
        + TryFrom<i64>
        + TryFrom<i128>;

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

    /// Creates an instance from the given `value`. Unlike the various `new...` functions, this
    /// will never fail as the value is masked to the result size.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn masked_new<T: Integer>(value: T) -> Self;

    /// Creates a number from the given value, throwing an error if the value is too large.
    /// This constructor is useful when the value is convertible to T. Use [`Self::new`] for literals.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn from_<T: Integer>(value: T) -> Self;

    /// Returns the number as a primitive data type.
    ///
    /// Note that if this is a signed negative number, the returned value may span more bits than
    /// [`BITS`](Self::BITS), as it preserves the numeric value instead of the bitwise value:
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// let value: i8 = i3::new(-1).value();
    /// assert_eq!(value, -1);
    /// assert_eq!(value.count_ones(), 8);
    /// ```
    ///
    /// If you need a value within the specified bit range, use [`to_bits`](Self::to_bits).
    #[must_use]
    fn value(self) -> Self::UnderlyingType;

    /// Returns the bitwise representation of the value. This method should be used when e.g. writing to bitfields.
    ///
    /// This is guaranteed to return the same value as [`value`](Self::value) for unsigned numbers.
    ///
    /// As the bit width is limited to [`BITS`](Self::BITS) the numeric value may differ from [`value`](Self::value)
    /// if this is a signed negative number:
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// let value = i3::new(-1);
    /// assert_eq!(value.to_bits(), 0b111);              // 7
    /// assert_eq!(value.value(), 0b1111_1111_u8 as i8); // -1
    /// ```
    ///
    /// To convert from the bitwise representation back to an instance, use [`from_bits`](Self::from_bits).
    #[must_use = "this returns the result of the operation, without modifying the original"]
    fn to_bits(self) -> Self::UnsignedUnderlyingType;

    /// Try to convert the bitwise representation from [`to_bits`](Self::to_bits) to an instance.
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// i3::try_from_bits(0b1111).expect_err("value is > 3 bits");
    /// let value = i3::try_from_bits(0b111).expect("value is <= 3 bits");
    /// assert_eq!(value.value(), -1);
    /// assert_eq!(value.to_bits(), 0b111);
    /// ```
    ///
    /// If you want to convert a numeric value to an instance instead, use [`try_new`](Self::try_new).
    ///
    /// # Errors
    ///
    /// Returns an error if the given value exceeds the bit width specified by [`BITS`](Self::BITS).
    fn try_from_bits(value: Self::UnsignedUnderlyingType) -> Result<Self, TryNewError>;

    /// Converts the bitwise representation from [`to_bits`](Self::to_bits) to an instance,
    /// without checking the bounds.
    ///
    /// # Safety
    ///
    /// The given value must not exceed the bit width specified by [`Self::BITS`].
    #[must_use]
    unsafe fn from_bits_unchecked(value: Self::UnsignedUnderlyingType) -> Self;

    /// Convert the bitwise representation from [`to_bits`](Self::to_bits) to an instance.
    ///
    /// ```
    /// # use arbitrary_int::prelude::*;
    /// let value = i3::from_bits(0b111);
    /// assert_eq!(value.value(), -1);
    /// assert_eq!(value.to_bits(), 0b111);
    /// ```
    ///
    /// If you want to convert a numeric value to an instance instead, use [`new`](Self::new).
    ///
    /// # Panics
    ///
    /// Panics if the given value exceeds the bit width specified by [`BITS`](Self::BITS).
    #[inline]
    #[must_use]
    fn from_bits(value: Self::UnsignedUnderlyingType) -> Self {
        match Self::try_from_bits(value) {
            Ok(value) => value,
            Err(_) => panic!("Value exceeds too many bits to fit within this integer type"),
        }
    }

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
