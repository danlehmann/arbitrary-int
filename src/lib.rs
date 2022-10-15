#![cfg_attr(not(feature = "std"), no_std)]

use core::fmt::{Debug, Display, Formatter};
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl,
    ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

struct CompileTimeAssert<const A: usize, const B: usize> {}

impl<const A: usize, const B: usize> CompileTimeAssert<A, B> {
    pub const SMALLER_OR_EQUAL: () = {
        assert!(A <= B);
    };
    pub const SMALLER_THAN: () = {
        assert!(A <= B);
    };
}

#[derive(Copy, Clone, Eq, PartialEq, Default, Ord, PartialOrd)]
pub struct UInt<T, const NUM_BITS: usize> {
    value: T,
}

impl<T, const NUM_BITS: usize> UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    /// Returns the type as a fundamental data type
    #[inline]
    pub const fn value(&self) -> T {
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

    fn mask() -> T {
        // It would be great if we could make this function const, but generic traits aren't compatible with
        // const fn
        // Also note that we have to use T::from(1) (as opposed to doing that at the end), as we
        // only require From(u8) in the generic constraints.
        let one = T::from(1);
        (one << NUM_BITS) - one
    }
}

// Next are specific implementations for u8, u16, u32, u64 and u128. A couple notes:
// - The existence of MAX also serves as a neat bounds-check for NUM_BITS: If NUM_BITS is too large,
//   the subtraction overflows which will fail to compile. This simplifies things a lot.
//   However, that only works if every constructor also uses MAX somehow (doing let _ = MAX is enough)

macro_rules! uint_impl {
    ($type:ident) => {
        impl<const NUM_BITS: usize> UInt<$type, NUM_BITS> {
            /// Minimum value that can be represented by this type
            pub const MIN: Self = Self { value: 0 };

            /// Maximum value that can be represented by this type
            /// Note that the existence of MAX also serves as a bounds check: If NUM_BITS is > available bits,
            /// we will get a compiler error right here
            pub const MAX: Self = Self {
                value: $type::MAX >> ($type::BITS as usize - NUM_BITS),
            };

            /// Creates an instance. Panics if the given value is outside of the valid range
            #[inline]
            pub const fn new(value: $type) -> Self {
                assert!(value <= Self::MAX.value);

                Self { value }
            }

            #[deprecated(note = "Use one of the specific functions like extract_u32")]
            pub const fn extract(value: $type, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= $type::BITS as usize);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: (value >> start_bit) & Self::MAX.value,
                }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient.
            /// panics if start_bit+<number of bits> doesn't fit within an u8, e.g. u5::extract_u8(8, 4);
            #[inline]
            pub const fn extract_u8(value: u8, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= 8);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: ((value >> start_bit) as $type) & Self::MAX.value,
                }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient
            /// panics if start_bit+<number of bits> doesn't fit within a u16, e.g. u15::extract_u16(8, 2);
            #[inline]
            pub const fn extract_u16(value: u16, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= 16);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: ((value >> start_bit) as $type) & Self::MAX.value,
                }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient
            /// panics if start_bit+<number of bits> doesn't fit within a u32, e.g. u30::extract_u32(8, 4);
            #[inline]
            pub const fn extract_u32(value: u32, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= 32);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: ((value >> start_bit) as $type) & Self::MAX.value,
                }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient
            /// panics if start_bit+<number of bits> doesn't fit within a u64, e.g. u60::extract_u64(8, 5);
            #[inline]
            pub const fn extract_u64(value: u64, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= 64);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: ((value >> start_bit) as $type) & Self::MAX.value,
                }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient
            /// panics if start_bit+<number of bits> doesn't fit within a u128, e.g. u120::extract_u64(8, 9);
            #[inline]
            pub const fn extract_u128(value: u128, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= 128);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self {
                    value: ((value >> start_bit) as $type) & Self::MAX.value,
                }
            }

            /// Returns a UInt with a wider bit depth but with the same base data type
            pub const fn widen<const NUM_BITS_RESULT: usize>(
                &self,
            ) -> UInt<$type, NUM_BITS_RESULT> {
                let _ = CompileTimeAssert::<NUM_BITS, NUM_BITS_RESULT>::SMALLER_THAN;
                // Query MAX of the result to ensure we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = UInt::<$type, NUM_BITS_RESULT>::MAX;
                UInt::<$type, NUM_BITS_RESULT> { value: self.value }
            }
        }
    };
}

uint_impl!(u8);
uint_impl!(u16);
uint_impl!(u32);
uint_impl!(u64);
uint_impl!(u128);

// Arithmetic implementations
impl<T, const NUM_BITS: usize> Add for UInt<T, NUM_BITS>
where
    T: PartialEq
        + Eq
        + Copy
        + BitAnd<T, Output = T>
        + Not<Output = T>
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value + rhs.value;
        #[cfg(debug_assertions)]
        if (sum & !Self::mask()) != T::from(0) {
            panic!("attempt to add with overflow");
        }
        Self {
            value: sum & Self::mask(),
        }
    }
}

impl<T, const NUM_BITS: usize> AddAssign for UInt<T, NUM_BITS>
where
    T: PartialEq
        + Eq
        + Not<Output = T>
        + Copy
        + AddAssign<T>
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + Sub<T, Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
{
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        #[cfg(debug_assertions)]
        if (self.value & !Self::mask()) != T::from(0) {
            panic!("attempt to add with overflow");
        }
        self.value &= Self::mask();
    }
}

impl<T, const NUM_BITS: usize> Sub for UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn sub(self, rhs: Self) -> Self::Output {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        Self {
            value: (self.value - rhs.value) & Self::mask(),
        }
    }
}

impl<T, const NUM_BITS: usize> SubAssign for UInt<T, NUM_BITS>
where
    T: Copy
        + SubAssign<T>
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    fn sub_assign(&mut self, rhs: Self) {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        self.value -= rhs.value;
        self.value &= Self::mask();
    }
}

impl<T, const NUM_BITS: usize> BitAnd for UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value & rhs.value,
        }
    }
}

impl<T, const NUM_BITS: usize> BitAndAssign for UInt<T, NUM_BITS>
where
    T: Copy + BitAndAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitand_assign(&mut self, rhs: Self) {
        self.value &= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> BitOr for UInt<T, NUM_BITS>
where
    T: Copy + BitOr<T, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value | rhs.value,
        }
    }
}

impl<T, const NUM_BITS: usize> BitOrAssign for UInt<T, NUM_BITS>
where
    T: Copy + BitOrAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitor_assign(&mut self, rhs: Self) {
        self.value |= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> BitXor for UInt<T, NUM_BITS>
where
    T: Copy + BitXor<T, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value ^ rhs.value,
        }
    }
}

impl<T, const NUM_BITS: usize> BitXorAssign for UInt<T, NUM_BITS>
where
    T: Copy + BitXorAssign<T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn bitxor_assign(&mut self, rhs: Self) {
        self.value ^= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> Not for UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + BitXor<T, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn not(self) -> Self::Output {
        Self {
            value: self.value ^ Self::mask(),
        }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> Shl<TSHIFTBITS> for UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + Shl<TSHIFTBITS, Output = T>
        + Sub<T, Output = T>
        + Shl<usize, Output = T>
        + Shr<usize, Output = T>
        + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn shl(self, rhs: TSHIFTBITS) -> Self::Output {
        Self {
            value: (self.value << rhs) & Self::mask(),
        }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> ShlAssign<TSHIFTBITS> for UInt<T, NUM_BITS>
where
    T: Copy
        + BitAnd<T, Output = T>
        + BitAndAssign<T>
        + ShlAssign<TSHIFTBITS>
        + Sub<T, Output = T>
        + Shr<usize, Output = T>
        + Shl<usize, Output = T>
        + From<u8>,
{
    fn shl_assign(&mut self, rhs: TSHIFTBITS) {
        self.value <<= rhs;
        self.value &= Self::mask();
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> Shr<TSHIFTBITS> for UInt<T, NUM_BITS>
where
    T: Copy + Shr<TSHIFTBITS, Output = T> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    type Output = UInt<T, NUM_BITS>;

    fn shr(self, rhs: TSHIFTBITS) -> Self::Output {
        Self {
            value: self.value >> rhs,
        }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> ShrAssign<TSHIFTBITS> for UInt<T, NUM_BITS>
where
    T: Copy + ShrAssign<TSHIFTBITS> + Sub<T, Output = T> + Shl<usize, Output = T> + From<u8>,
{
    fn shr_assign(&mut self, rhs: TSHIFTBITS) {
        self.value >>= rhs;
    }
}

impl<T, const NUM_BITS: usize> Display for UInt<T, NUM_BITS>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T, const NUM_BITS: usize> Debug for UInt<T, NUM_BITS>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

// Conversions
macro_rules! from_impl {
    ($target_type:ident, $source_type:ident) => {
        impl<const NUM_BITS: usize, const NUM_BITS_FROM: usize>
            From<UInt<$source_type, NUM_BITS_FROM>> for UInt<$target_type, NUM_BITS>
        {
            fn from(item: UInt<$source_type, NUM_BITS_FROM>) -> Self {
                let _ = CompileTimeAssert::<NUM_BITS_FROM, NUM_BITS>::SMALLER_OR_EQUAL;
                Self {
                    value: item.value as $target_type,
                }
            }
        }
    };
}

from_impl!(u8, u16);
from_impl!(u8, u32);
from_impl!(u8, u64);
from_impl!(u8, u128);

from_impl!(u16, u8);
from_impl!(u16, u32);
from_impl!(u16, u64);
from_impl!(u16, u128);

from_impl!(u32, u8);
from_impl!(u32, u16);
from_impl!(u32, u64);
from_impl!(u32, u128);

from_impl!(u64, u8);
from_impl!(u64, u16);
from_impl!(u64, u32);
from_impl!(u64, u128);

from_impl!(u128, u8);
from_impl!(u128, u16);
from_impl!(u128, u32);
from_impl!(u128, u64);

// Define type aliases like u1, u63 and u80 using the smallest possible underlying data type.
// These are for convenience only - UInt<u32, 15> is still legal
macro_rules! type_alias {
    ($n:expr, $name:ident, $type:ident) => {
        #[allow(non_camel_case_types)]
        pub type $name = UInt<$type, $n>;
    };
}

type_alias!(1, u1, u8);
type_alias!(2, u2, u8);
type_alias!(3, u3, u8);
type_alias!(4, u4, u8);
type_alias!(5, u5, u8);
type_alias!(6, u6, u8);
type_alias!(7, u7, u8);

type_alias!(9, u9, u16);
type_alias!(10, u10, u16);
type_alias!(11, u11, u16);
type_alias!(12, u12, u16);
type_alias!(13, u13, u16);
type_alias!(14, u14, u16);
type_alias!(15, u15, u16);

type_alias!(17, u17, u32);
type_alias!(18, u18, u32);
type_alias!(19, u19, u32);
type_alias!(20, u20, u32);
type_alias!(21, u21, u32);
type_alias!(22, u22, u32);
type_alias!(23, u23, u32);
type_alias!(24, u24, u32);
type_alias!(25, u25, u32);
type_alias!(26, u26, u32);
type_alias!(27, u27, u32);
type_alias!(28, u28, u32);
type_alias!(29, u29, u32);
type_alias!(30, u30, u32);
type_alias!(31, u31, u32);

type_alias!(33, u33, u64);
type_alias!(34, u34, u64);
type_alias!(35, u35, u64);
type_alias!(36, u36, u64);
type_alias!(37, u37, u64);
type_alias!(38, u38, u64);
type_alias!(39, u39, u64);
type_alias!(40, u40, u64);
type_alias!(41, u41, u64);
type_alias!(42, u42, u64);
type_alias!(43, u43, u64);
type_alias!(44, u44, u64);
type_alias!(45, u45, u64);
type_alias!(46, u46, u64);
type_alias!(47, u47, u64);
type_alias!(48, u48, u64);
type_alias!(49, u49, u64);
type_alias!(50, u50, u64);
type_alias!(51, u51, u64);
type_alias!(52, u52, u64);
type_alias!(53, u53, u64);
type_alias!(54, u54, u64);
type_alias!(55, u55, u64);
type_alias!(56, u56, u64);
type_alias!(57, u57, u64);
type_alias!(58, u58, u64);
type_alias!(59, u59, u64);
type_alias!(60, u60, u64);
type_alias!(61, u61, u64);
type_alias!(62, u62, u64);
type_alias!(63, u63, u64);

type_alias!(65, u65, u128);
type_alias!(66, u66, u128);
type_alias!(67, u67, u128);
type_alias!(68, u68, u128);
type_alias!(69, u69, u128);
type_alias!(70, u70, u128);
type_alias!(71, u71, u128);
type_alias!(72, u72, u128);
type_alias!(73, u73, u128);
type_alias!(74, u74, u128);
type_alias!(75, u75, u128);
type_alias!(76, u76, u128);
type_alias!(77, u77, u128);
type_alias!(78, u78, u128);
type_alias!(79, u79, u128);
type_alias!(80, u80, u128);
type_alias!(81, u81, u128);
type_alias!(82, u82, u128);
type_alias!(83, u83, u128);
type_alias!(84, u84, u128);
type_alias!(85, u85, u128);
type_alias!(86, u86, u128);
type_alias!(87, u87, u128);
type_alias!(88, u88, u128);
type_alias!(89, u89, u128);
type_alias!(90, u90, u128);
type_alias!(91, u91, u128);
type_alias!(92, u92, u128);
type_alias!(93, u93, u128);
type_alias!(94, u94, u128);
type_alias!(95, u95, u128);
type_alias!(96, u96, u128);
type_alias!(97, u97, u128);
type_alias!(98, u98, u128);
type_alias!(99, u99, u128);
type_alias!(100, u100, u128);
type_alias!(101, u101, u128);
type_alias!(102, u102, u128);
type_alias!(103, u103, u128);
type_alias!(104, u104, u128);
type_alias!(105, u105, u128);
type_alias!(106, u106, u128);
type_alias!(107, u107, u128);
type_alias!(108, u108, u128);
type_alias!(109, u109, u128);
type_alias!(110, u110, u128);
type_alias!(111, u111, u128);
type_alias!(112, u112, u128);
type_alias!(113, u113, u128);
type_alias!(114, u114, u128);
type_alias!(115, u115, u128);
type_alias!(116, u116, u128);
type_alias!(117, u117, u128);
type_alias!(118, u118, u128);
type_alias!(119, u119, u128);
type_alias!(120, u120, u128);
type_alias!(121, u121, u128);
type_alias!(122, u122, u128);
type_alias!(123, u123, u128);
type_alias!(124, u124, u128);
type_alias!(125, u125, u128);
type_alias!(126, u126, u128);
type_alias!(127, u127, u128);
