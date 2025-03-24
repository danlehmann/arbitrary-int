//! This module contains the few bits of functionality that can be shared between Int's and UInt's.

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
