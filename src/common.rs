//! This module contains the functionality that can be shared between [`crate::Int`] and [`crate::UInt`]

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
            pub const fn swap_bytes(self) -> Self {
                // swap_bytes() of the underlying type does most of the work. Then, we just need to shift
                Self {
                    value: self.value.swap_bytes() >> Self::UNUSED_BITS,
                }
            }

            pub const fn to_le_bytes(self) -> [u8; Self::BITS >> 3] {
                let mut result = [0_u8; Self::BITS >> 3];
                let be = self.value.to_le_bytes();
                crate::common::const_byte_copy::<{ Self::BITS >> 3 }, 0, 0>(&mut result, &be);
                result
            }

            pub const fn to_be_bytes(self) -> [u8; Self::BITS >> 3] {
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
            pub const fn to_ne_bytes(self) -> [u8; Self::BITS >> 3] {
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

/// Implement [`core::iter::Step`] (if the `step_trait` feature is enabled).
macro_rules! impl_step {
    ($type:tt) => {
        #[cfg(feature = "step_trait")]
        impl<T, const BITS: usize> core::iter::Step for $type<T, BITS>
        where
            Self: Integer<UnderlyingType = T>,
            T: Copy + core::iter::Step,
        {
            #[inline]
            fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                core::iter::Step::steps_between(&start.value(), &end.value())
            }

            #[inline]
            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                if let Some(res) = core::iter::Step::forward_checked(start.value(), count) {
                    Self::try_new(res).ok()
                } else {
                    None
                }
            }

            #[inline]
            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                if let Some(res) = core::iter::Step::backward_checked(start.value(), count) {
                    Self::try_new(res).ok()
                } else {
                    None
                }
            }
        }
    };
}

pub(crate) use impl_step;

/// Implement support for the `borsh` crate (if the feature is enabled)
macro_rules! impl_borsh {
    ($type:ident, $declaration_prefix:literal) => {
        #[cfg(feature = "borsh")]
        impl<T, UnsignedT, const BITS: usize> borsh::BorshSerialize for $type<T, BITS>
        where
            // These bounds are a bit more complex than they need to be for unsigned integers,
            // but functionally that doesn't make a difference. This allows us to share the implementation.
            Self: Integer<UnsignedUnderlyingType = UnsignedT>,
            UnsignedT: borsh::BorshSerialize,
        {
            #[inline]
            fn serialize<W: borsh::io::Write>(&self, writer: &mut W) -> borsh::io::Result<()> {
                // Ideally, we'd want a buffer of size `BITS >> 3` or `size_of::<T>`, but that's not possible
                // with arrays at present (`feature(generic_const_exprs)`, once stable, will allow this).
                // `vec!` would be an option, but an allocation is not expected at this level.
                // Therefore, allocate a buffer big enough to fit any underlying type and take a slice out of it.
                const BUFFER_SIZE: usize = size_of::<u128>();
                let mut buffer = [0_u8; BUFFER_SIZE];
                const {
                    // This causes a compiler error if the buffer isn't big enough. That isn't possible with any
                    // of the types provided by this crate, but it can't hurt to double check.
                    assert!(core::mem::size_of::<UnsignedT>() <= BUFFER_SIZE);
                }

                let serialized_byte_count = BITS.div_ceil(8);
                self.to_bits().serialize(&mut buffer.as_mut_slice())?;
                writer.write_all(&buffer[..serialized_byte_count])
            }
        }

        #[cfg(feature = "borsh")]
        impl<T, UnsignedT, const BITS: usize> borsh::BorshDeserialize for $type<T, BITS>
        where
            // These bounds are a bit more complex than they need to be for unsigned integers,
            // but functionally that doesn't make a difference. This allows us to share the implementation.
            Self: Integer<UnsignedUnderlyingType = UnsignedT>,
            UnsignedT: borsh::BorshDeserialize,
        {
            #[inline]
            fn deserialize_reader<R: borsh::io::Read>(reader: &mut R) -> borsh::io::Result<Self> {
                // Ideally, we'd want a buffer of size `BITS >> 3` or `size_of::<T>`, but that's not possible
                // with arrays at present (`feature(generic_const_exprs)`, once stable, will allow this).
                // `vec!` would be an option, but an allocation is not expected at this level.
                // Therefore, allocate a buffer big enough to fit any underlying type and take a slice out of it.
                const BUFFER_SIZE: usize = size_of::<u128>();
                let mut buffer = [0_u8; BUFFER_SIZE];
                const {
                    // This causes a compiler error if the buffer isn't big enough. That isn't possible with any
                    // of the types provided by this crate, but it can't hurt to double check.
                    assert!(core::mem::size_of::<UnsignedT>() <= BUFFER_SIZE);
                }

                let serialized_byte_count = BITS.div_ceil(8);
                let underlying_byte_count = core::mem::size_of::<UnsignedT>();

                // Read from the source, advancing cursor by the exact right number of bytes
                reader.read_exact(&mut buffer[..serialized_byte_count])?;

                // Deserialize the underlying type. We have to pass in the correct number of bytes of the
                // underlying type (or more, but let's be precise). The unused bytes are all still zero
                let value = UnsignedT::deserialize(&mut &buffer[..underlying_byte_count])?;

                Self::try_from_bits(value).map_err(|_| {
                    borsh::io::Error::new(borsh::io::ErrorKind::InvalidData, "Value out of range")
                })
            }
        }

        #[cfg(feature = "borsh")]
        impl<T, const BITS: usize> borsh::BorshSchema for $type<T, BITS> {
            #[inline]
            fn add_definitions_recursively(
                definitions: &mut alloc::collections::btree_map::BTreeMap<
                    borsh::schema::Declaration,
                    borsh::schema::Definition,
                >,
            ) {
                let byte_count = BITS.div_ceil(8) as u8;
                let def = borsh::schema::Definition::Primitive(byte_count);
                definitions.insert(Self::declaration(), def);
            }

            #[inline]
            fn declaration() -> borsh::schema::Declaration {
                use alloc::string::ToString;
                [$declaration_prefix, &BITS.to_string()].concat()
            }
        }
    };
}

pub(crate) use impl_borsh;

/// Implements support for the `num-traits` crate, if the feature is enabled.
macro_rules! impl_num_traits {
    ($type:ident, $primitive_8:ty, |$result:ident| $limit_result:expr) => {
        #[cfg(feature = "num-traits")]
        impl<T, const BITS: usize> num_traits::WrappingAdd for $type<T, BITS>
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
                + From<$primitive_8>,
            core::num::Wrapping<T>: Add<core::num::Wrapping<T>, Output = core::num::Wrapping<T>>,
        {
            #[inline]
            fn wrapping_add(&self, rhs: &Self) -> Self {
                let $result =
                    (core::num::Wrapping(self.value()) + core::num::Wrapping(rhs.value())).0;
                Self {
                    value: $limit_result,
                }
            }
        }

        #[cfg(feature = "num-traits")]
        impl<T, const BITS: usize> num_traits::WrappingSub for $type<T, BITS>
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
                + From<$primitive_8>,
            core::num::Wrapping<T>: Sub<core::num::Wrapping<T>, Output = core::num::Wrapping<T>>,
        {
            #[inline]
            fn wrapping_sub(&self, rhs: &Self) -> Self {
                let $result =
                    (core::num::Wrapping(self.value()) - core::num::Wrapping(rhs.value())).0;
                Self {
                    value: $limit_result,
                }
            }
        }

        #[cfg(feature = "num-traits")]
        impl<T, const BITS: usize> num_traits::bounds::Bounded for $type<T, BITS>
        where
            Self: Integer,
        {
            #[inline]
            fn min_value() -> Self {
                Self::MIN
            }

            #[inline]
            fn max_value() -> Self {
                Self::MAX
            }
        }
    };
}

pub(crate) use impl_num_traits;
