#![cfg_attr(not(feature = "std"), no_std)]

mod lib {
    pub mod core {
        #[cfg(not(feature = "std"))]
        pub use core::*;
        #[cfg(feature = "std")]
        pub use std::*;
    }
}

use seq_macro::seq;
use lib::core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

struct CompileTimeAssert<const A: usize, const B: usize> {}

impl<const A: usize, const B: usize> CompileTimeAssert<A, B> {
    pub const SMALLER_OR_EQUAL: () = { assert!(A <= B); };
    pub const SMALLER_THAN: () = { assert!(A <= B); };
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Default, Ord, PartialOrd)]
pub struct UInt<T, const NUM_BITS: usize> {
    value: T,
}

impl<T, const NUM_BITS: usize> UInt<T, NUM_BITS>
    where T: Copy + BitAnd<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    pub const fn value(&self) -> T { self.value }

    pub const unsafe fn new_unchecked(value: T) -> Self { Self { value } }

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
//   the left shift overflows which will fail to compile. This simplifies things a lot.
//   However, that only works if every constructor also uses MAX somehow (doing let _ = MAX is enough)

macro_rules! uint_impl {
    ($size:expr, $type:ident) => {

        impl<const NUM_BITS: usize> UInt<$type, NUM_BITS> {
            /// Minimum value that can be represented by this type
            pub const MIN: Self = Self { value: 0 };

            /// Maximum value that can be represented by this type
            /// Note that the existence of MAX also serves as a bounds check: If NUM_BITS is >= available bits,
            /// we will get a compiler error right here
            pub const MAX: Self = Self { value: (1 << NUM_BITS) - 1 };

            /// Creates an instance. Panics if the given value is outside of the valid range
            pub const fn new(value: $type) -> Self {
                assert!(value <= Self::MAX.value);

                Self { value }
            }

            /// Extracts bits from a given value. The extract is equivalent to: `new((value >> start_bit) & MASK)`
            /// Unlike new, extract doesn't perform range-checking so it is slightly more efficient
            pub const fn extract(value: $type, start_bit: usize) -> Self {
                assert!(start_bit + NUM_BITS <= $size);
                // Query MAX to ensure that we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = Self::MAX;

                Self { value: (value >> start_bit) & Self::MAX.value }
            }

            /// Returns a UInt with a wider bit depth but with the same base data type
            pub const fn widen<const NUM_BITS_RESULT: usize>(&self) -> UInt<$type, NUM_BITS_RESULT> {
                let _ = CompileTimeAssert::<NUM_BITS, NUM_BITS_RESULT>::SMALLER_THAN;
                // Query MAX of the result to ensure we get a compiler error if the current definition is bogus (e.g. <u8, 9>)
                let _ = UInt::<$type, NUM_BITS_RESULT>::MAX;
                UInt::<$type, NUM_BITS_RESULT> { value: self.value }
            }
        }
    }
}

uint_impl!(8, u8);
uint_impl!(16, u16);
uint_impl!(32, u32);
uint_impl!(64, u64);
uint_impl!(128, u128);

// Arithmetic implementations
impl<T, const NUM_BITS: usize> Add for UInt<T, NUM_BITS>
    where T: PartialEq + Eq + Copy + BitAnd<T, Output=T> + Not<Output=T> + Add<T, Output=T> + Sub<T, Output=T> + Shr<usize, Output=T> + Shl<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn add(self, rhs: Self) -> Self::Output {
        let sum = self.value + rhs.value;
        #[cfg(debug_assertions)]
        if (sum & !Self::mask()) != T::from(0) {
            panic!("attempt to add with overflow");
        }
        Self { value: sum & Self::mask() }
    }
}

impl<T, const NUM_BITS: usize> AddAssign for UInt<T, NUM_BITS>
    where T: PartialEq + Eq + Not<Output=T> + Copy + AddAssign<T> + BitAnd<T, Output=T> + BitAndAssign<T> + Sub<T, Output=T> + Shr<usize, Output=T> + Shl<usize, Output=T> + From<u8> {
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
    where T: Copy + BitAnd<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn sub(self, rhs: Self) -> Self::Output {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        Self { value: (self.value - rhs.value) & Self::mask() }
    }
}

impl<T, const NUM_BITS: usize> SubAssign for UInt<T, NUM_BITS>
    where T: Copy + SubAssign<T> + BitAnd<T, Output=T> + BitAndAssign<T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    fn sub_assign(&mut self, rhs: Self) {
        // No need for extra overflow checking as the regular minus operator already handles it for us
        self.value -= rhs.value;
        self.value &= Self::mask();
    }
}

impl<T, const NUM_BITS: usize> BitAnd for UInt<T, NUM_BITS>
    where T: Copy + BitAnd<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self { value: self.value & rhs.value }
    }
}

impl<T, const NUM_BITS: usize> BitAndAssign for UInt<T, NUM_BITS>
    where T: Copy + BitAndAssign<T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    fn bitand_assign(&mut self, rhs: Self) {
        self.value &= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> BitOr for UInt<T, NUM_BITS>
    where T: Copy + BitOr<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self { value: self.value | rhs.value }
    }
}

impl<T, const NUM_BITS: usize> BitOrAssign for UInt<T, NUM_BITS>
    where T: Copy + BitOrAssign<T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    fn bitor_assign(&mut self, rhs: Self) {
        self.value |= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> BitXor for UInt<T, NUM_BITS>
    where T: Copy + BitXor<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self { value: self.value ^ rhs.value }
    }
}

impl<T, const NUM_BITS: usize> BitXorAssign for UInt<T, NUM_BITS>
    where T: Copy + BitXorAssign<T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.value ^= rhs.value;
    }
}

impl<T, const NUM_BITS: usize> Not for UInt<T, NUM_BITS>
    where T: Copy + BitAnd<T, Output=T> + BitXor<T, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn not(self) -> Self::Output {
        Self { value: self.value ^ Self::mask() }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> Shl<TSHIFTBITS> for UInt<T, NUM_BITS>
    where T: Copy + BitAnd<T, Output=T> + Shl<TSHIFTBITS, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + Shr<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn shl(self, rhs: TSHIFTBITS) -> Self::Output {
        Self { value: (self.value << rhs) & Self::mask() }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> ShlAssign<TSHIFTBITS> for UInt<T, NUM_BITS>
    where T: Copy + BitAnd<T, Output=T> + BitAndAssign<T> + ShlAssign<TSHIFTBITS> + Sub<T, Output=T> + Shr<usize, Output=T> + Shl<usize, Output=T> + From<u8> {
    fn shl_assign(&mut self, rhs: TSHIFTBITS) {
        self.value <<= rhs;
        self.value &= Self::mask();
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> Shr<TSHIFTBITS> for UInt<T, NUM_BITS>
    where T: Copy + Shr<TSHIFTBITS, Output=T> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    type Output = UInt<T, NUM_BITS>;

    fn shr(self, rhs: TSHIFTBITS) -> Self::Output {
        Self { value: self.value >> rhs }
    }
}

impl<T, TSHIFTBITS, const NUM_BITS: usize> ShrAssign<TSHIFTBITS> for UInt<T, NUM_BITS>
    where T: Copy + ShrAssign<TSHIFTBITS> + Sub<T, Output=T> + Shl<usize, Output=T> + From<u8> {
    fn shr_assign(&mut self, rhs: TSHIFTBITS) {
        self.value >>= rhs;
    }
}

// Conversions
macro_rules! from_impl {
    ($target_type:ident, $source_type:ident) => {

        impl<const NUM_BITS: usize, const NUM_BITS_FROM: usize> From<UInt<$source_type, NUM_BITS_FROM>> for UInt<$target_type, NUM_BITS> {
            fn from(item: UInt<$source_type, NUM_BITS_FROM>) -> Self {
                let _ = CompileTimeAssert::<NUM_BITS_FROM, NUM_BITS>::SMALLER_OR_EQUAL;
                Self { value: item.value as $target_type }
            }
        }
    }
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
seq!(N in 1..=7 {
    #[allow(non_camel_case_types)]
    pub type u~N = UInt<u8, N>;
});

seq!(N in 9..=15 {
    #[allow(non_camel_case_types)]
    pub type u~N = UInt<u16, N>;
});

seq!(N in 17..=31 {
    #[allow(non_camel_case_types)]
    pub type u~N = UInt<u32, N>;
});

seq!(N in 33..=63 {
    #[allow(non_camel_case_types)]
    pub type u~N = UInt<u64, N>;
});

seq!(N in 65..=127 {
    #[allow(non_camel_case_types)]
    pub type u~N = UInt<u128, N>;
});
