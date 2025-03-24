use crate::{
    common::{from_arbitrary_int_impl, from_native_impl, impl_extract},
    TryNewError,
};
use core::{
    fmt::{self, Debug},
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait SignedNumber: Sized + Copy + Clone + PartialOrd + Ord + PartialEq + Eq {
    type UnderlyingType: SignedNumber
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

    /// Returns the type as a fundamental data type
    ///
    /// Note that if negative, the returned value may span more bits than [`Self::BITS`],
    /// as it preserves the numeric value instead of the bitwise value:
    /// ```
    /// # use arbitrary_int::i3;
    /// let value: i8 = i3::new(-1).value();
    /// assert_eq!(value, -1);
    /// assert_eq!(value.count_ones(), 8);
    /// ```
    /// If you need a value within the specified bit range, use [`Int::to_bits`].
    fn value(self) -> Self::UnderlyingType;

    /// Creates a number from the given value, throwing an error if the value is too large.
    /// This constructor is useful when the value is convertible to T. Use [`Self::new`] for literals.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn from_<T: SignedNumber>(value: T) -> Self;

    /// Creates an instance from the given `value`. Unlike the various `new...` functions, this
    /// will never fail as the value is masked to the result size.
    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    fn masked_new<T: SignedNumber>(value: T) -> Self;

    fn as_i8(&self) -> i8;

    fn as_i16(&self) -> i16;

    fn as_i32(&self) -> i32;

    fn as_i64(&self) -> i64;

    fn as_i128(&self) -> i128;

    fn as_isize(&self) -> isize;

    #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
    #[inline]
    fn as_<T: SignedNumber>(self) -> T {
        T::masked_new(self)
    }
}

macro_rules! impl_signed_number_native {
    // `$const_keyword` is marked as an optional fragment here so that it can conditionally be put on the impl.
    // This macro will be invoked with `i8 as const, ...` if `const_convert_and_const_trait_impl` is enabled.
    ($($type:ident $(as $const_keyword:ident)?),+) => {
        $(
            impl $($const_keyword)? SignedNumber for $type {
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
                fn from_<T: SignedNumber>(value: T) -> Self {
                    if T::BITS > Self::BITS as usize {
                        assert!(value >= T::masked_new(Self::MIN) && value <= T::masked_new(Self::MAX));
                    }
                    Self::masked_new(value)
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                #[inline]
                fn masked_new<T: SignedNumber>(value: T) -> Self {
                    // Primitive types don't need masking
                    match Self::BITS {
                        8 => value.as_i8() as Self,
                        16 => value.as_i16() as Self,
                        32 => value.as_i32() as Self,
                        64 => value.as_i64() as Self,
                        128 => value.as_i128() as Self,
                        _ => panic!("Unhandled Number type")
                    }
                }

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
impl_signed_number_native!(i8, i16, i32, i64, i128);

#[cfg(feature = "const_convert_and_const_trait_impl")]
impl_signed_number_native!(i8 as const, i16 as const, i32 as const, i64 as const, i128 as const);

#[derive(Copy, Clone, Eq, PartialEq, Default, Ord, PartialOrd)]
pub struct Int<T, const BITS: usize> {
    value: T,
}

impl<T: Copy, const BITS: usize> Int<T, BITS> {
    /// The number of bits in the underlying type that are not present in this type.
    const UNUSED_BITS: usize = ((core::mem::size_of::<T>() << 3) - Self::BITS);

    pub const BITS: usize = BITS;

    /// Returns the type as a fundamental data type
    ///
    /// Note that if negative, the returned value may span more bits than [`Self::BITS`],
    /// as it preserves the numeric value instead of the bitwise value:
    /// ```
    /// # use arbitrary_int::i3;
    /// let value: i8 = i3::new(-1).value();
    /// assert_eq!(value, -1);
    /// assert_eq!(value.count_ones(), 8);
    /// ```
    /// If you need a value within the specified bit range, use [`Self::to_bits`].
    #[cfg(not(feature = "hint"))]
    #[inline]
    pub const fn value(self) -> T {
        self.value
    }

    /// Initializes a new value without checking the bounds
    ///
    /// # Safety
    /// Must only be called with a value bigger or equal to [`Self::MIN`] and less than or equal to [`Self::MAX`].
    #[inline]
    pub const unsafe fn new_unchecked(value: T) -> Self {
        Self { value }
    }
}

macro_rules! int_impl_num {
    // `$const_keyword` is marked as an optional fragment here so that it can conditionally be put on the impl.
    // This macro will be invoked with `i8 as const, ...` if `const_convert_and_const_trait_impl` is enabled.
    ($($type:ident $(as $const_keyword:ident)?),+) => {
        $(
            impl<const BITS: usize> $($const_keyword)? SignedNumber for Int<$type, BITS> {
                type UnderlyingType = $type;

                const BITS: usize = BITS;

                const MIN: Self = Self { value: -Self::MAX.value - 1 };

                // The existence of MAX also serves as a bounds check: If NUM_BITS is > available bits,
                // we will get a compiler error right here
                const MAX: Self = Self {
                    // MAX is always positive so we don't have to worry about the sign
                    value: (<$type as SignedNumber>::MAX >> (<$type as SignedNumber>::BITS - Self::BITS)),
                };

                #[inline]
                fn try_new(value: Self::UnderlyingType) -> Result<Self, TryNewError> {
                    if value >= Self::MIN.value && value <= Self::MAX.value {
                        Ok(Self { value })
                    } else {
                        Err(TryNewError{})
                    }
                }

                #[inline]
                fn new(value: $type) -> Self {
                    assert!(value >= Self::MIN.value && value <= Self::MAX.value);

                    Self { value }
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                #[inline]
                fn from_<T: SignedNumber>(value: T) -> Self {
                    if Self::BITS < T::BITS {
                        assert!(value >= Self::MIN.value.as_() && value <= Self::MAX.value.as_());
                    }
                    Self { value: Self::UnderlyingType::masked_new(value) }
                }

                #[cfg(not(feature = "const_convert_and_const_trait_impl"))]
                fn masked_new<T: SignedNumber>(value: T) -> Self {
                    if Self::BITS < T::BITS {
                        let value = (value.as_::<Self::UnderlyingType>() << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
                        Self { value: Self::UnderlyingType::masked_new(value) }
                    } else {
                        Self { value: Self::UnderlyingType::masked_new(value) }
                    }
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
                        core::hint::assert_unchecked(self.value >= Self::MIN.value);
                        core::hint::assert_unchecked(self.value <= Self::MAX.value);
                    }

                    self.value
                }
            }
        )+
    };
}

#[cfg(not(feature = "const_convert_and_const_trait_impl"))]
int_impl_num!(i8, i16, i32, i64, i128);

#[cfg(feature = "const_convert_and_const_trait_impl")]
int_impl_num!(i8 as const, i16 as const, i32 as const, i64 as const, i128 as const);

macro_rules! int_impl {
    ($(($type:ident, $unsigned_type:ident)),+) => {
        $(
            impl<const BITS: usize> Int<$type, BITS> {
                pub const MASK: $type = (Self::MAX.value << 1) | 1;

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn new(value: $type) -> Self {
                    assert!(value >= Self::MIN.value && value <= Self::MAX.value);

                    Self { value }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_i8(value: i8) -> Self {
                    if Self::BITS < 8 {
                        assert!(value >= Self::MIN.value as i8 && value <= Self::MAX.value as i8);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_i16(value: i16) -> Self {
                    if Self::BITS < 16 {
                        assert!(value >= Self::MIN.value as i16 && value <= Self::MAX.value as i16);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_i32(value: i32) -> Self {
                    if Self::BITS < 32 {
                        assert!(value >= Self::MIN.value as i32 && value <= Self::MAX.value as i32);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_i64(value: i64) -> Self {
                    if Self::BITS < 64 {
                        assert!(value >= Self::MIN.value as i64 && value <= Self::MAX.value as i64);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance. Panics if the given value is outside of the valid range
                #[inline]
                pub const fn from_i128(value: i128) -> Self {
                    if Self::BITS < 128 {
                        assert!(value >= Self::MIN.value as i128 && value <= Self::MAX.value as i128);
                    }
                    Self { value: value as $type }
                }

                /// Creates an instance or an error if the given value is outside of the valid range
                #[inline]
                pub const fn try_new(value: $type) -> Result<Self, TryNewError> {
                    if value >= Self::MIN.value && value <= Self::MAX.value {
                        Ok(Self { value })
                    } else {
                        Err(TryNewError {})
                    }
                }

                /// Returns the bitwise representation of the value
                ///
                /// As the bit width is limited to [`Self::BITS`] the numeric value may differ from [`Self::value`]:
                /// ```
                /// # use arbitrary_int::i3;
                /// let value = i3::new(-1);
                /// assert_eq!(value.to_bits(), 0b111); // 7
                /// assert_eq!(value.value(), -1);
                /// ```
                /// To convert from the bitwise representation back to an instance, use [`Self::from_bits`].
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn to_bits(self) -> $unsigned_type {
                    (self.value() & Self::MASK) as $unsigned_type
                }

                /// Convert the bitwise representation from [`Self::to_bits`] to an instance
                ///
                /// ```
                /// # use arbitrary_int::i3;
                /// let value = i3::from_bits(0b111);
                /// assert_eq!(value.value(), -1);
                /// assert_eq!(value.to_bits(), 0b111);
                /// ```
                /// If you want to convert a numeric value to an instance instead, use [`Self::new`].
                ///
                /// # Panics
                /// Panics if the given value exceeds the bit width specified by [`Self::BITS`].
                #[inline]
                pub const fn from_bits(value: $unsigned_type) -> Self {
                    assert!(value & (!Self::MASK as $unsigned_type) == 0);

                    // First do a logical left shift to put the sign bit at the underlying type's MSB (copying the sign),
                    // then an arithmetic right shift to sign-extend the value into its original position.
                    Self { value: ((value << Self::UNUSED_BITS) as $type) >> Self::UNUSED_BITS }
                }

                /// Tries to convert the bitwise representation from [`Self::to_bits`] to an instance
                ///
                /// ```
                /// # use arbitrary_int::i3;
                /// i3::try_from_bits(0b1111).expect_err("value is > 3 bits");
                /// let value = i3::try_from_bits(0b111).expect("value is <= 3 bits");
                /// assert_eq!(value.value(), -1);
                /// assert_eq!(value.to_bits(), 0b111);
                /// ```
                /// If you want to convert a numeric value to an instance instead, use [`Self::try_new`].
                ///
                /// # Errors
                /// Returns an error if the given value exceeds the bit width specified by [`Self::BITS`].
                #[inline]
                pub const fn try_from_bits(value: $unsigned_type) -> Result<Self, TryNewError> {
                    if value & (!Self::MASK as $unsigned_type) == 0 {
                        // First do a logical left shift to put the sign bit at the underlying type's MSB (copying the sign),
                        // then an arithmetic right shift to sign-extend the value into its original position.
                        Ok(Self { value: ((value << Self::UNUSED_BITS) as $type) >> Self::UNUSED_BITS })
                    } else {
                        Err(TryNewError {})
                    }
                }

                /// Converts the bitwise representation from [`Self::to_bits`] to an instance, without checking the bounds
                ///
                /// # Safety
                /// The given value must not exceed the bit width specified by [`Self::BITS`].
                #[inline]
                pub const unsafe fn from_bits_unchecked(value: $unsigned_type) -> Self {
                    // First do a logical left shift to put the sign bit at the underlying type's MSB (copying the sign),
                    // then an arithmetic right shift to sign-extend the value into its original position.
                    Self { value: ((value << Self::UNUSED_BITS) as $type) >> Self::UNUSED_BITS }
                }

                /// Returns the type as a fundamental data type
                ///
                /// Note that if negative, the returned value may span more bits than [`Self::BITS`],
                /// as it preserves the numeric value instead of the bitwise value:
                /// ```
                /// # use arbitrary_int::i3;
                /// let value: i8 = i3::new(-1).value();
                /// assert_eq!(value, -1);
                /// assert_eq!(value.count_ones(), 8);
                /// ```
                /// If you need a value within the specified bit range, use [`Self::to_bits`].
                #[cfg(feature = "hint")]
                #[inline]
                pub const fn value(self) -> $type {
                    // The hint feature requires the type to be const-comparable,
                    // which isn't possible in the generic version above. So we have
                    // an entirely different function if this feature is enabled.
                    // It only works for primitive types, which should be ok in practice
                    // (but is technically an API change)
                    unsafe {
                        core::hint::assert_unchecked(self.value >= Self::MIN.value);
                        core::hint::assert_unchecked(self.value <= Self::MAX.value);
                    }
                    self.value
                }

                // Generate the `extract_{i,u}{8,16,32,64,128}` functions.
                impl_extract!(
                    $type,
                    "from_bits(value >> start_bit)",
                    |value| (value << Self::UNUSED_BITS) >> Self::UNUSED_BITS,

                    (8, (i8, extract_i8), (u8, extract_u8)),
                    (16, (i16, extract_i16), (u16, extract_u16)),
                    (32, (i32, extract_i32), (u32, extract_u32)),
                    (64, (i64, extract_i64), (u64, extract_u64)),
                    (128, (i128, extract_i128), (u128, extract_u128))
                );

                /// Returns an [`Int`] with a wider bit depth but with the same base data type
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn widen<const BITS_RESULT: usize>(self) -> Int<$type, BITS_RESULT> {
                    const { assert!(BITS < BITS_RESULT, "Can not call widen() with the given bit widths") };

                    // Query MAX of the result to ensure we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                    let _ = Int::<$type, BITS_RESULT>::MAX;
                    Int::<$type, BITS_RESULT> { value: self.value }
                }

                /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(100).wrapping_add(i14::new(27)), i14::new(127));
                /// assert_eq!(i14::MAX.wrapping_add(i14::new(2)), i14::MIN + i14::new(1));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_add(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_add(rhs.value);
                    Self {
                        value: (sum << Self::UNUSED_BITS) >> Self::UNUSED_BITS,
                    }
                }

                /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(0).wrapping_sub(i14::new(127)), i14::new(-127));
                /// assert_eq!(i14::new(-2).wrapping_sub(i14::MAX), i14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_sub(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_sub(rhs.value);
                    Self {
                        value: (sum << Self::UNUSED_BITS) >> Self::UNUSED_BITS,
                    }
                }

                /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i14;
                /// assert_eq!(i14::new(10).wrapping_mul(i14::new(12)), i14::new(120));
                /// assert_eq!(i14::new(12).wrapping_mul(i14::new(1024)), i14::new(-4096));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_mul(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_mul(rhs.value);
                    Self {
                        value: (sum << Self::UNUSED_BITS) >> Self::UNUSED_BITS,
                    }
                }

                /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the
                /// boundary of the type.
                ///
                /// The only case where such wrapping can occur is when one divides `MIN / -1` on a
                /// signed type (where `MIN` is the negative minimal value for the type); this is
                /// equivalent to `-MIN`, a positive value that is too large to represent in the type.
                /// In such a case, this function returns `MIN` itself.
                ///
                /// # Panics
                ///
                /// This function will panic if `rhs` is zero.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(100).wrapping_div(i14::new(10)), i14::new(10));
                /// assert_eq!(i14::MIN.wrapping_div(i14::new(-1)), i14::MIN);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_div(self, rhs: Self) -> Self {
                    let sum = self.value.wrapping_div(rhs.value);
                    Self {
                        // Unlike the unsigned implementation we do need to account for overflow here,
                        // `Self::MIN / -1` is equal to `Self::MAX + 1`.
                        value: (sum << Self::UNUSED_BITS) >> Self::UNUSED_BITS,
                    }
                }

                /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where mask removes any
                /// high-order bits of `rhs` that would cause the shift to exceed the bitwidth of the type.
                ///
                /// Note that this is not the same as a rotate-left; the RHS of a wrapping shift-left is
                /// restricted to the range of the type, rather than the bits shifted out of the LHS being
                /// returned to the other end.
                /// A [`rotate_left`](Self::rotate_left) function exists as well, which may be what you
                /// want instead.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i14;
                /// assert_eq!(i14::new(-1).wrapping_shl(7), i14::new(-128));
                /// assert_eq!(i14::new(-1).wrapping_shl(128), i14::new(-4));
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn wrapping_shl(self, rhs: u32) -> Self {
                    // modulo is expensive on some platforms, so only do it when necessary
                    let shift_amount = Self::UNUSED_BITS as u32 + (if rhs >= BITS as u32 {
                        rhs % (BITS as u32)
                    } else {
                        rhs
                    });

                    Self {
                        // We could use wrapping_shl here to make Debug builds slightly smaller;
                        // the downside would be that on weird CPUs that don't do wrapping_shl by
                        // default release builds would get slightly worse. Using << should give
                        // good release performance everywere
                        value: (self.value << shift_amount) >> Self::UNUSED_BITS,
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
                /// ```
                /// # use arbitrary_int::i14;
                /// assert_eq!(i14::new(-128).wrapping_shr(7), i14::new(-1));
                /// assert_eq!(i14::new(-128).wrapping_shr(60), i14::new(-8));
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
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(100).saturating_add(i14::new(1)), i14::new(101));
                /// assert_eq!(i14::MAX.saturating_add(i14::new(100)), i14::MAX);
                /// assert_eq!(i14::MIN.saturating_add(i14::new(-1)), i14::MIN);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_add(self, rhs: Self) -> Self {
                    if Self::UNUSED_BITS == 0 {
                        // We are something like a Int::<i8; 8>, we can fallback to the base implementation.
                        // This is very unlikely to happen in practice, but checking allows us to use
                        // `wrapping_add` instead of `saturating_add` in the common case, which is faster.
                        let value = self.value.saturating_add(rhs.value);
                        Self { value }
                    } else {
                        // We're dealing with fewer bits than the underlying type (e.g. i7).
                        // That means the addition can never overflow the underlying type.
                        let value = self.value.wrapping_add(rhs.value);
                        if value > Self::MAX.value {
                            Self::MAX
                        } else if value < Self::MIN.value {
                            Self::MIN
                        } else {
                            Self { value }
                        }
                    }
                }

                /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(100).saturating_sub(i14::new(127)), i14::new(-27));
                /// assert_eq!(i14::MIN.saturating_sub(i14::new(100)), i14::MIN);
                /// assert_eq!(i14::MAX.saturating_sub(i14::new(-1)), i14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_sub(self, rhs: Self) -> Self {
                    if Self::UNUSED_BITS == 0 {
                        // We are something like a Int::<i8; 8>, we can fallback to the base implementation.
                        // This is very unlikely to happen in practice, but checking allows us to use
                        // `wrapping_sub` instead of `saturating_sub` in the common case, which is faster.
                        let value = self.value.saturating_sub(rhs.value);
                        Self { value }
                    } else {
                        // We're dealing with fewer bits than the underlying type (e.g. i7).
                        // That means the subtraction can never overflow the underlying type.
                        let value = self.value.wrapping_sub(rhs.value);
                        if value > Self::MAX.value {
                            Self::MAX
                        } else if value < Self::MIN.value {
                            Self::MIN
                        } else {
                            Self { value }
                        }
                    }
                }

                /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(10).saturating_mul(i14::new(12)), i14::new(120));
                /// assert_eq!(i14::MAX.saturating_mul(i14::new(10)), i14::MAX);
                /// assert_eq!(i14::MIN.saturating_mul(i14::new(10)), i14::MIN);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_mul(self, rhs: Self) -> Self {
                    let value = if BITS << 1 <= (core::mem::size_of::<$type>() << 3) {
                        // We have half the bits (e.g. i4 * i4) of the base type, so we can't overflow the base type
                        // `wrapping_mul` likely provides the best performance on all cpus
                        self.value.wrapping_mul(rhs.value)
                    } else {
                        // We have more than half the bits (e.g. i6 * i6)
                        self.value.saturating_mul(rhs.value)
                    };

                    if value > Self::MAX.value {
                        Self::MAX
                    } else if value < Self::MIN.value {
                        Self::MIN
                    } else {
                        Self { value }
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
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(5).saturating_div(i14::new(2)), i14::new(2));
                /// assert_eq!(i14::MAX.saturating_div(i14::new(-1)), i14::MIN + i14::new(1));
                /// assert_eq!(i14::MIN.saturating_div(i14::new(-1)), i14::MAX);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_div(self, rhs: Self) -> Self {
                    // As `Self::MIN / -1` is equal to `Self::MAX + 1` we always need to check for overflow.
                    let value = self.value.saturating_div(rhs.value);

                    if value > Self::MAX.value {
                        Self::MAX
                    } else if value < Self::MIN.value {
                        Self::MIN
                    } else {
                        Self { value }
                    }
                }

                /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric
                /// bounds instead of overflowing.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i14, SignedNumber};
                /// assert_eq!(i14::new(-4).saturating_pow(3), i14::new(-64));
                /// assert_eq!(i14::MIN.saturating_pow(2), i14::MAX);
                /// assert_eq!(i14::MIN.saturating_pow(3), i14::MIN);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn saturating_pow(self, exp: u32) -> Self {
                    // It might be possible to handwrite this to be slightly faster as both
                    // `saturating_pow` has to do a bounds-check and then we do second one.
                    let value = self.value.saturating_pow(exp);

                    if value > Self::MAX.value {
                        Self::MAX
                    } else if value < Self::MIN.value {
                        Self::MIN
                    } else {
                        Self { value }
                    }
                }

                /// Reverses the order of bits in the integer. The least significant bit becomes the most
                /// significant bit, second least-significant bit becomes second most-significant bit, etc.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i6;
                /// assert_eq!(i6::from_bits(0b10_1010).reverse_bits(), i6::from_bits(0b01_0101));
                /// assert_eq!(i6::new(0), i6::new(0).reverse_bits());
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn reverse_bits(self) -> Self {
                    let value = self.value().reverse_bits() >> Self::UNUSED_BITS;
                    Self { value }
                }

                /// Returns the number of ones in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::from_bits(0b00_1000);
                /// assert_eq!(n.count_ones(), 1);
                /// ```
                #[inline]
                pub const fn count_ones(self) -> u32 {
                    // Due to sign-extension the unused bits may be either all ones or zeros, so we need to mask them off.
                    (self.value() & Self::MASK).count_ones()
                }

                /// Returns the number of zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::{i6, SignedNumber};
                /// assert_eq!(i6::MAX.count_zeros(), 1);
                /// ```
                #[inline]
                pub const fn count_zeros(self) -> u32 {
                    // Due to sign-extension the unused bits may be either all ones or zeros, so we need to mask them off.
                    // Afterwards the unused bits are all zero, so we can subtract them from the result.
                    // We can avoid a bounds check in debug builds with `wrapping_sub` since this cannot overflow.
                    (self.value() & Self::MASK).count_zeros().wrapping_sub(Self::UNUSED_BITS as u32)
                }

                /// Returns the number of leading ones in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::new(-1);
                /// assert_eq!(n.leading_ones(), 6);
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
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::new(-1);
                /// assert_eq!(n.leading_zeros(), 0);
                /// ```
                #[inline]
                pub const fn leading_zeros(self) -> u32 {
                    if Self::UNUSED_BITS == 0 {
                        self.value().leading_zeros()
                    } else {
                        // Prevent an all-zero value reporting the underlying type's entire bit width by setting
                        // the first unused bit to one, causing `leading_zeros()` to ignore all unused bits.
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
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::new(3);
                /// assert_eq!(n.trailing_ones(), 2);
                /// ```
                #[inline]
                pub const fn trailing_ones(self) -> u32 {
                    // Prevent an all-ones value reporting the underlying type's entire bit width by masking
                    // off all the unused bits.
                    (self.value() & Self::MASK).trailing_ones()
                }

                /// Returns the number of trailing zeros in the binary representation of `self`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::new(-4);
                /// assert_eq!(n.trailing_zeros(), 2);
                /// ```
                #[inline]
                pub const fn trailing_zeros(self) -> u32 {
                    // Prevent an all-ones value reporting the underlying type's entire bit width by setting
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
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::from_bits(0b10_1010);
                /// let m = i6::from_bits(0b01_0101);
                ///
                /// assert_eq!(n.rotate_left(1), m);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn rotate_left(self, n: u32) -> Self {
                    let b = BITS as u32;
                    let n = if n >= b { n % b } else { n };

                    // Temporarily switch to an unsigned type to prevent sign-extension with `>>`.
                    let moved_bits = ((self.value() << n) & Self::MASK) as $unsigned_type;
                    let truncated_bits = ((self.value() & Self::MASK) as $unsigned_type) >> (b - n);
                    let value = (((moved_bits | truncated_bits) << Self::UNUSED_BITS) as $type) >> Self::UNUSED_BITS;
                    Self { value }
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
                /// ```
                /// # use arbitrary_int::i6;
                /// let n = i6::from_bits(0b10_1010);
                /// let m = i6::from_bits(0b01_0101);
                ///
                /// assert_eq!(n.rotate_right(1), m);
                /// ```
                #[inline]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                pub const fn rotate_right(self, n: u32) -> Self {
                    let b = BITS as u32;
                    let n = if n >= b { n % b } else { n };

                    // Temporarily switch to an unsigned type to prevent sign-extension with `>>`.
                    let moved_bits = (self.value() & Self::MASK) as $unsigned_type >> n;
                    let truncated_bits = ((self.value() << (b - n)) & Self::MASK) as $unsigned_type;
                    let value = (((moved_bits | truncated_bits) << Self::UNUSED_BITS) as $type) >> Self::UNUSED_BITS;
                    Self { value }
                }
            }
        )+
    };
}

int_impl!((i8, u8), (i16, u16), (i32, u32), (i64, u64), (i128, u128));

// Arithmetic operator implementations
impl<T, const BITS: usize> Add for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Add<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value + rhs.value;
        let value = (sum << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
        debug_assert!(sum == value, "attempted to add with overflow");
        Self { value }
    }
}

impl<T, const BITS: usize> AddAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Add<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    fn add_assign(&mut self, rhs: Self) {
        // Delegate to the Add implementation above.
        *self = *self + rhs;
    }
}

impl<T, const BITS: usize> Sub for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Sub<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let difference = self.value - rhs.value;
        let value = (difference << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
        debug_assert!(difference == value, "attempted to subtract with overflow");
        Self { value }
    }
}

impl<T, const BITS: usize> SubAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Sub<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    fn sub_assign(&mut self, rhs: Self) {
        // Delegate to the Sub implementation above.
        *self = *self - rhs;
    }
}

impl<T, const BITS: usize> Mul for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Mul<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.value * rhs.value;
        let value = (product << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
        debug_assert!(product == value, "attempted to multiply with overflow");
        Self { value }
    }
}

impl<T, const BITS: usize> MulAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Mul<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    fn mul_assign(&mut self, rhs: Self) {
        // Delegate to the Mul implementation above.
        *self = *self * rhs;
    }
}

impl<T, const BITS: usize> Div for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Div<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        // Unlike the unsigned implementation we do need to account for overflow here,
        // `Self::MIN / -1` is equal to `Self::MAX + 1` and should therefore panic.
        let quotient = self.value / rhs.value;
        let value = (quotient << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
        debug_assert!(quotient == value, "attempted to divide with overflow");
        Self { value }
    }
}

impl<T, const BITS: usize> DivAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Div<T, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
{
    fn div_assign(&mut self, rhs: Self) {
        // Delegate to the Div implementation above.
        *self = *self / rhs;
    }
}

// Bitwise operator implementations
impl<T, const BITS: usize> BitAnd for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitAnd<T, Output = T>,
{
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let value = self.value & rhs.value;
        Self { value }
    }
}

impl<T, const BITS: usize> BitAndAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitAndAssign<T>,
{
    fn bitand_assign(&mut self, rhs: Self) {
        self.value &= rhs.value;
    }
}

impl<T, const BITS: usize> BitOr for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitOr<T, Output = T>,
{
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let value = self.value | rhs.value;
        Self { value }
    }
}

impl<T, const BITS: usize> BitOrAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitOrAssign<T>,
{
    fn bitor_assign(&mut self, rhs: Self) {
        self.value |= rhs.value;
    }
}

impl<T, const BITS: usize> BitXor for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitXor<T, Output = T>,
{
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let value = self.value ^ rhs.value;
        Self { value }
    }
}

impl<T, const BITS: usize> BitXorAssign for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + BitXorAssign<T>,
{
    fn bitxor_assign(&mut self, rhs: Self) {
        self.value ^= rhs.value;
    }
}

impl<T, const BITS: usize> Not for Int<T, BITS>
where
    Self: SignedNumber,
    T: PartialEq + Copy + Not<Output = T>,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        let value = !self.value;
        Self { value }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> Shl<TSHIFTBITS> for Int<T, BITS>
where
    Self: SignedNumber,
    T: Copy + Shl<TSHIFTBITS, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    type Output = Self;

    fn shl(self, rhs: TSHIFTBITS) -> Self::Output {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        debug_assert!(
            rhs.try_into().unwrap_or(usize::MAX) < BITS,
            "attempted to shift left with overflow"
        );

        // Shift left twice to avoid needing an unnecessarily strict `TSHIFTBITS: Add<Self::UNUSED_BITS>` bound.
        // This should be optimised to a single shift.
        let value = ((self.value << rhs) << Self::UNUSED_BITS) >> Self::UNUSED_BITS;
        Self { value }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> ShlAssign<TSHIFTBITS> for Int<T, BITS>
where
    Self: SignedNumber,
    T: Copy + Shl<TSHIFTBITS, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    fn shl_assign(&mut self, rhs: TSHIFTBITS) {
        // Delegate to the Shl implementation above.
        *self = *self << rhs;
    }
}

impl<T, TSHIFTBITS, const BITS: usize> Shr<TSHIFTBITS> for Int<T, BITS>
where
    Self: SignedNumber,
    T: Copy + Shr<TSHIFTBITS, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    type Output = Self;

    fn shr(self, rhs: TSHIFTBITS) -> Self::Output {
        // With debug assertions, the << and >> operators throw an exception if the shift amount
        // is larger than the number of bits (in which case the result would always be 0)
        debug_assert!(
            rhs.try_into().unwrap_or(usize::MAX) < BITS,
            "attempted to shift right with overflow"
        );

        Self {
            // Our unused bits can only ever all be 1 or 0, depending on the sign.
            // As right shifts on primitive types perform sign-extension anyways we don't need to do any extra work here.
            value: self.value >> rhs,
        }
    }
}

impl<T, TSHIFTBITS, const BITS: usize> ShrAssign<TSHIFTBITS> for Int<T, BITS>
where
    Self: SignedNumber,
    T: Copy + Shr<TSHIFTBITS, Output = T> + Shl<usize, Output = T> + Shr<usize, Output = T>,
    TSHIFTBITS: TryInto<usize> + Copy,
{
    fn shr_assign(&mut self, rhs: TSHIFTBITS) {
        // Delegate to the Shr implementation above.
        *self = *self >> rhs;
    }
}

// Delegated trait implementations
impl<T, const BITS: usize> fmt::Display for Int<T, BITS>
where
    T: fmt::Display,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> fmt::Debug for Int<T, BITS>
where
    T: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> fmt::LowerHex for Int<T, BITS>
where
    T: fmt::LowerHex,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> fmt::UpperHex for Int<T, BITS>
where
    T: fmt::UpperHex,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> fmt::Octal for Int<T, BITS>
where
    T: fmt::Octal,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const BITS: usize> fmt::Binary for Int<T, BITS>
where
    T: fmt::Binary,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

#[cfg(feature = "defmt")]
impl<T, const BITS: usize> defmt::Format for Int<T, BITS>
where
    T: defmt::Format,
{
    #[inline]
    fn format(&self, f: defmt::Formatter) {
        self.value.format(f)
    }
}

// Serde's invalid_value error (https://rust-lang.github.io/hashbrown/serde/de/trait.Error.html#method.invalid_value)
// takes an Unexpected (https://rust-lang.github.io/hashbrown/serde/de/enum.Unexpected.html) which only accepts a 64 bit
// integer. This is a problem for us because we want to support 128 bit integers. To work around this we define our own
// error type using the Int's underlying type which implements Display and then use serde::de::Error::custom to create
// an error with our custom type.
#[cfg(feature = "serde")]
struct InvalidIntValueError<T>
where
    T: SignedNumber,
    T::UnderlyingType: fmt::Display,
{
    value: T::UnderlyingType,
}

#[cfg(feature = "serde")]
impl<T> fmt::Display for InvalidIntValueError<T>
where
    T: SignedNumber,
    T::UnderlyingType: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid value: integer `{}`, expected a value between `{}` and `{}`",
            self.value,
            T::MIN.value(),
            T::MAX.value()
        )
    }
}

#[cfg(feature = "serde")]
impl<T, const BITS: usize> serde::Serialize for Int<T, BITS>
where
    T: serde::Serialize,
{
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.value.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T, const BITS: usize> serde::Deserialize<'de> for Int<T, BITS>
where
    Self: SignedNumber<UnderlyingType = T>,
    T: fmt::Display + PartialOrd + serde::Deserialize<'de>,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = T::deserialize(deserializer)?;

        if value >= Self::MIN.value && value <= Self::MAX.value {
            Ok(Self { value })
        } else {
            let err = InvalidIntValueError::<Self> { value };
            Err(serde::de::Error::custom(err))
        }
    }
}

// Conversions
from_arbitrary_int_impl!(Int(i8), [i16, i32, i64, i128]);
from_arbitrary_int_impl!(Int(i16), [i8, i32, i64, i128]);
from_arbitrary_int_impl!(Int(i32), [i8, i16, i64, i128]);
from_arbitrary_int_impl!(Int(i64), [i8, i16, i32, i128]);
from_arbitrary_int_impl!(Int(i128), [i8, i32, i64, i16]);

from_native_impl!(Int(i8), [i8, i16, i32, i64, i128]);
from_native_impl!(Int(i16), [i8, i16, i32, i64, i128]);
from_native_impl!(Int(i32), [i8, i16, i32, i64, i128]);
from_native_impl!(Int(i64), [i8, i16, i32, i64, i128]);
from_native_impl!(Int(i128), [i8, i16, i32, i64, i128]);

pub use aliases::*;

#[allow(non_camel_case_types)]
#[rustfmt::skip]
pub(crate) mod aliases {
    use crate::common::type_alias;

    type_alias!(Int(i8), (i1, 1), (i2, 2), (i3, 3), (i4, 4), (i5, 5), (i6, 6), (i7, 7));
    type_alias!(Int(i16), (i9, 9), (i10, 10), (i11, 11), (i12, 12), (i13, 13), (i14, 14), (i15, 15));
    type_alias!(Int(i32), (i17, 17), (i18, 18), (i19, 19), (i20, 20), (i21, 21), (i22, 22), (i23, 23), (i24, 24), (i25, 25), (i26, 26), (i27, 27), (i28, 28), (i29, 29), (i30, 30), (i31, 31));
    type_alias!(Int(i64), (i33, 33), (i34, 34), (i35, 35), (i36, 36), (i37, 37), (i38, 38), (i39, 39), (i40, 40), (i41, 41), (i42, 42), (i43, 43), (i44, 44), (i45, 45), (i46, 46), (i47, 47), (i48, 48), (i49, 49), (i50, 50), (i51, 51), (i52, 52), (i53, 53), (i54, 54), (i55, 55), (i56, 56), (i57, 57), (i58, 58), (i59, 59), (i60, 60), (i61, 61), (i62, 62), (i63, 63));
    type_alias!(Int(i128), (i65, 65), (i66, 66), (i67, 67), (i68, 68), (i69, 69), (i70, 70), (i71, 71), (i72, 72), (i73, 73), (i74, 74), (i75, 75), (i76, 76), (i77, 77), (i78, 78), (i79, 79), (i80, 80), (i81, 81), (i82, 82), (i83, 83), (i84, 84), (i85, 85), (i86, 86), (i87, 87), (i88, 88), (i89, 89), (i90, 90), (i91, 91), (i92, 92), (i93, 93), (i94, 94), (i95, 95), (i96, 96), (i97, 97), (i98, 98), (i99, 99), (i100, 100), (i101, 101), (i102, 102), (i103, 103), (i104, 104), (i105, 105), (i106, 106), (i107, 107), (i108, 108), (i109, 109), (i110, 110), (i111, 111), (i112, 112), (i113, 113), (i114, 114), (i115, 115), (i116, 116), (i117, 117), (i118, 118), (i119, 119), (i120, 120), (i121, 121), (i122, 122), (i123, 123), (i124, 124), (i125, 125), (i126, 126), (i127, 127));
}
