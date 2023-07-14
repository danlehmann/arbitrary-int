#![cfg_attr(feature = "step_trait", feature(step_trait))]

extern crate core;

use arbitrary_int::*;
use std::collections::HashMap;
#[cfg(feature = "step_trait")]
use std::iter::Step;

#[test]
fn constants() {
    // Make a constant to ensure new().value() works in a const-context
    const TEST_CONSTANT: u8 = u7::new(127).value();
    assert_eq!(TEST_CONSTANT, 127u8);

    // Same with widen()
    const TEST_CONSTANT2: u7 = u6::new(63).widen();
    assert_eq!(TEST_CONSTANT2, u7::new(63));

    // Same with widen()
    const TEST_CONSTANT3A: Result<u6, TryNewError> = u6::try_new(62);
    assert_eq!(TEST_CONSTANT3A, Ok(u6::new(62)));
    const TEST_CONSTANT3B: Result<u6, TryNewError> = u6::try_new(64);
    assert!(TEST_CONSTANT3B.is_err());
}

#[test]
fn create_simple() {
    let value7 = u7::new(123);
    let value8 = UInt::<u8, 8>::new(189);

    let value13 = u13::new(123);
    let value16 = UInt::<u16, 16>::new(60000);

    let value23 = u23::new(123);
    let value67 = u67::new(123);

    assert_eq!(value7.value(), 123);
    assert_eq!(value8.value(), 189);

    assert_eq!(value13.value(), 123);
    assert_eq!(value16.value(), 60000);

    assert_eq!(value23.value(), 123);
    assert_eq!(value67.value(), 123);
}

#[test]
fn create_try_new() {
    assert_eq!(u7::new(123).value(), 123);
    assert_eq!(u7::try_new(190).expect_err("No error seen"), TryNewError {});
}

#[test]
#[should_panic]
fn create_panic_u7() {
    u7::new(128);
}

#[test]
#[should_panic]
fn create_panic_u15() {
    u15::new(32768);
}

#[test]
#[should_panic]
fn create_panic_u31() {
    u31::new(2147483648);
}

#[test]
#[should_panic]
fn create_panic_u63() {
    u63::new(0x8000_0000_0000_0000);
}

#[test]
#[should_panic]
fn create_panic_u127() {
    u127::new(0x8000_0000_0000_0000_0000_0000_0000_0000);
}

#[test]
fn add() {
    assert_eq!(u7::new(10) + u7::new(20), u7::new(30));
    assert_eq!(u7::new(100) + u7::new(27), u7::new(127));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn add_overflow() {
    let _ = u7::new(127) + u7::new(3);
}

#[cfg(not(debug_assertions))]
#[test]
fn add_no_overflow() {
    let _ = u7::new(127) + u7::new(3);
}

#[cfg(feature = "num-traits")]
#[test]
fn num_traits_add_wrapping() {
    let v1 = u7::new(120);
    let v2 = u7::new(10);
    let v3 = num_traits::WrappingAdd::wrapping_add(&v1, &v2);
    assert_eq!(v3, u7::new(2));
}

#[cfg(feature = "num-traits")]
#[test]
fn num_traits_sub_wrapping() {
    let v1 = u7::new(15);
    let v2 = u7::new(20);
    let v3 = num_traits::WrappingSub::wrapping_sub(&v1, &v2);
    assert_eq!(v3, u7::new(123));
}

#[cfg(feature = "num-traits")]
#[test]
fn num_traits_bounded() {
    use num_traits::bounds::Bounded;
    assert_eq!(u7::MAX, u7::max_value());
    assert_eq!(u119::MAX, u119::max_value());
    assert_eq!(u7::new(0), u7::min_value());
    assert_eq!(u119::new(0), u119::min_value());
}

#[test]
fn addassign() {
    let mut value = u9::new(500);
    value += u9::new(11);
    assert_eq!(value, u9::new(511));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn addassign_overflow() {
    let mut value = u9::new(500);
    value += u9::new(40);
}

#[cfg(not(debug_assertions))]
#[test]
fn addassign_no_overflow() {
    let mut value = u9::new(500);
    value += u9::new(40);
}

#[test]
fn sub() {
    assert_eq!(u7::new(22) - u7::new(10), u7::new(12));
    assert_eq!(u7::new(127) - u7::new(127), u7::new(0));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn sub_overflow() {
    let _ = u7::new(100) - u7::new(127);
}

#[cfg(not(debug_assertions))]
#[test]
fn sub_no_overflow() {
    let _ = u7::new(100) - u7::new(127);
}

#[test]
fn subassign() {
    let mut value = u9::new(500);
    value -= u9::new(11);
    assert_eq!(value, u9::new(489));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn subassign_overflow() {
    let mut value = u9::new(30);
    value -= u9::new(40);
}

#[cfg(not(debug_assertions))]
#[test]
fn subassign_no_overflow() {
    let mut value = u9::new(30);
    value -= u9::new(40);
}

#[test]
fn bitand() {
    assert_eq!(
        u17::new(0b11001100) & u17::new(0b01101001),
        u17::new(0b01001000)
    );
    assert_eq!(u17::new(0b11001100) & u17::new(0), u17::new(0));
    assert_eq!(
        u17::new(0b11001100) & u17::new(0x1_FFFF),
        u17::new(0b11001100)
    );
}

#[test]
fn bitandassign() {
    let mut value = u4::new(0b0101);
    value &= u4::new(0b0110);
    assert_eq!(value, u4::new(0b0100));
}

#[test]
fn bitor() {
    assert_eq!(
        u17::new(0b11001100) | u17::new(0b01101001),
        u17::new(0b11101101)
    );
    assert_eq!(u17::new(0b11001100) | u17::new(0), u17::new(0b11001100));
    assert_eq!(
        u17::new(0b11001100) | u17::new(0x1_FFFF),
        u17::new(0x1_FFFF)
    );
}

#[test]
fn bitorassign() {
    let mut value = u4::new(0b0101);
    value |= u4::new(0b0110);
    assert_eq!(value, u4::new(0b0111));
}

#[test]
fn bitxor() {
    assert_eq!(
        u17::new(0b11001100) ^ u17::new(0b01101001),
        u17::new(0b10100101)
    );
    assert_eq!(u17::new(0b11001100) ^ u17::new(0), u17::new(0b11001100));
    assert_eq!(
        u17::new(0b11001100) ^ u17::new(0x1_FFFF),
        u17::new(0b1_11111111_00110011)
    );
}

#[test]
fn bitxorassign() {
    let mut value = u4::new(0b0101);
    value ^= u4::new(0b0110);
    assert_eq!(value, u4::new(0b0011));
}

#[test]
fn not() {
    assert_eq!(!u17::new(0), u17::new(0b1_11111111_11111111));
    assert_eq!(!u5::new(0b10101), u5::new(0b01010));
}

#[test]
fn shl() {
    assert_eq!(u17::new(0b1) << 5u8, u17::new(0b100000));
    // Ensure bits on the left are shifted out
    assert_eq!(u9::new(0b11110000) << 3u64, u9::new(0b1_10000000));
}

#[test]
fn shlassign() {
    let mut value = u9::new(0b11110000);
    value <<= 3;
    assert_eq!(value, u9::new(0b1_10000000));
}

#[test]
fn shr() {
    assert_eq!(u17::new(0b100110) >> 5usize, u17::new(1));

    // Ensure there's no sign extension
    assert_eq!(u17::new(0b1_11111111_11111111) >> 8, u17::new(0b1_11111111));
}

#[test]
fn shrassign() {
    let mut value = u9::new(0b1_11110000);
    value >>= 6;
    assert_eq!(value, u9::new(0b0_00000111));
}

#[test]
fn compare() {
    assert_eq!(true, u4::new(0b1100) > u4::new(0b0011));
    assert_eq!(true, u4::new(0b1100) >= u4::new(0b0011));
    assert_eq!(false, u4::new(0b1100) < u4::new(0b0011));
    assert_eq!(false, u4::new(0b1100) <= u4::new(0b0011));
    assert_eq!(true, u4::new(0b1100) != u4::new(0b0011));
    assert_eq!(false, u4::new(0b1100) == u4::new(0b0011));

    assert_eq!(false, u4::new(0b1100) > u4::new(0b1100));
    assert_eq!(true, u4::new(0b1100) >= u4::new(0b1100));
    assert_eq!(false, u4::new(0b1100) < u4::new(0b1100));
    assert_eq!(true, u4::new(0b1100) <= u4::new(0b1100));
    assert_eq!(false, u4::new(0b1100) != u4::new(0b1100));
    assert_eq!(true, u4::new(0b1100) == u4::new(0b1100));

    assert_eq!(false, u4::new(0b0011) > u4::new(0b1100));
    assert_eq!(false, u4::new(0b0011) >= u4::new(0b1100));
    assert_eq!(true, u4::new(0b0011) < u4::new(0b1100));
    assert_eq!(true, u4::new(0b0011) <= u4::new(0b1100));
    assert_eq!(true, u4::new(0b0011) != u4::new(0b1100));
    assert_eq!(false, u4::new(0b0011) == u4::new(0b1100));
}

#[test]
fn min_max() {
    assert_eq!(0, u4::MIN.value());
    assert_eq!(0b1111, u4::MAX.value());
    assert_eq!(u4::new(0b1111), u4::MAX);

    assert_eq!(0, u15::MIN.value());
    assert_eq!(32767, u15::MAX.value());
    assert_eq!(u15::new(32767), u15::MAX);

    assert_eq!(0, u31::MIN.value());
    assert_eq!(2147483647, u31::MAX.value());

    assert_eq!(0, u63::MIN.value());
    assert_eq!(0x7FFF_FFFF_FFFF_FFFF, u63::MAX.value());

    assert_eq!(0, u127::MIN.value());
    assert_eq!(0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, u127::MAX.value());
}

#[test]
fn bits() {
    assert_eq!(4, u4::BITS);
    assert_eq!(12, u12::BITS);
    assert_eq!(120, u120::BITS);
    assert_eq!(13, UInt::<u128, 13usize>::BITS);

    assert_eq!(8, u8::BITS);
    assert_eq!(16, u16::BITS);
}

#[test]
fn mask() {
    assert_eq!(0x1u8, u1::MASK);
    assert_eq!(0xFu8, u4::MASK);
    assert_eq!(0x3FFFFu32, u18::MASK);
    assert_eq!(0x7FFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFFu128, u127::MASK);
    assert_eq!(0x7FFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFFu128, u127::MASK);
    assert_eq!(0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFFu128, u128::MAX);
}

#[test]
fn min_max_fullwidth() {
    assert_eq!(u8::MIN, UInt::<u8, 8>::MIN.value());
    assert_eq!(u8::MAX, UInt::<u8, 8>::MAX.value());

    assert_eq!(u16::MIN, UInt::<u16, 16>::MIN.value());
    assert_eq!(u16::MAX, UInt::<u16, 16>::MAX.value());

    assert_eq!(u32::MIN, UInt::<u32, 32>::MIN.value());
    assert_eq!(u32::MAX, UInt::<u32, 32>::MAX.value());

    assert_eq!(u64::MIN, UInt::<u64, 64>::MIN.value());
    assert_eq!(u64::MAX, UInt::<u64, 64>::MAX.value());

    assert_eq!(u128::MIN, UInt::<u128, 128>::MIN.value());
    assert_eq!(u128::MAX, UInt::<u128, 128>::MAX.value());
}

#[allow(deprecated)]
#[test]
fn extract() {
    assert_eq!(u5::new(0b10000), u5::extract(0b11110000, 0));
    assert_eq!(u5::new(0b11100), u5::extract(0b11110000, 2));
    assert_eq!(u5::new(0b11110), u5::extract(0b11110000, 3));

    // Use extract with a custom type (5 bits of u32)
    assert_eq!(
        UInt::<u32, 5>::new(0b11110),
        UInt::<u32, 5>::extract(0b11110000, 3)
    );
    assert_eq!(
        u5::new(0b11110),
        UInt::<u32, 5>::extract(0b11110000, 3).into()
    );
}

#[test]
fn extract_typed() {
    assert_eq!(u5::new(0b10000), u5::extract_u8(0b11110000, 0));
    assert_eq!(u5::new(0b00011), u5::extract_u16(0b11110000_11110110, 6));
    assert_eq!(
        u5::new(0b01011),
        u5::extract_u32(0b11110010_11110110_00000000_00000000, 22)
    );
    assert_eq!(
        u5::new(0b01011),
        u5::extract_u64(
            0b11110010_11110110_00000000_00000000_00000000_00000000_00000000_00000000,
            54
        )
    );
    assert_eq!(u5::new(0b01011), u5::extract_u128(0b11110010_11110110_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000, 118));
}

#[test]
fn extract_full_width_typed() {
    assert_eq!(
        0b1010_0011,
        UInt::<u8, 8>::extract_u8(0b1010_0011, 0).value()
    );
    assert_eq!(
        0b1010_0011,
        UInt::<u8, 8>::extract_u16(0b1111_1111_1010_0011, 0).value()
    );
}

#[test]
#[should_panic]
fn extract_not_enough_bits_8() {
    let _ = u5::extract_u8(0b11110000, 4);
}

#[test]
#[should_panic]
fn extract_not_enough_bits_8_full_width() {
    let _ = UInt::<u8, 8>::extract_u8(0b11110000, 1);
}

#[test]
#[should_panic]
fn extract_not_enough_bits_16() {
    let _ = u5::extract_u16(0b11110000, 12);
}

#[test]
#[should_panic]
fn extract_not_enough_bits_32() {
    let _ = u5::extract_u32(0b11110000, 28);
}

#[test]
#[should_panic]
fn extract_not_enough_bits_64() {
    let _ = u5::extract_u64(0b11110000, 60);
}

#[test]
#[should_panic]
fn extract_not_enough_bits_128() {
    let _ = u5::extract_u128(0b11110000, 124);
}

#[test]
fn from_same_bit_widths() {
    assert_eq!(u5::from(UInt::<u8, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u16, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u32, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u64, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u128, 5>::new(0b10101)), u5::new(0b10101));

    assert_eq!(
        UInt::<u8, 8>::from(UInt::<u128, 8>::new(0b1110_0101)),
        UInt::<u8, 8>::new(0b1110_0101)
    );

    assert_eq!(
        UInt::<u16, 6>::from(UInt::<u8, 5>::new(0b10101)),
        UInt::<u16, 6>::new(0b10101)
    );
    assert_eq!(u15::from(UInt::<u16, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u32, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u64, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u128, 15>::new(0b10101)), u15::new(0b10101));

    assert_eq!(
        UInt::<u32, 6>::from(u6::new(0b10101)),
        UInt::<u32, 6>::new(0b10101)
    );
    assert_eq!(
        UInt::<u32, 14>::from(u14::new(0b10101)),
        UInt::<u32, 14>::new(0b10101)
    );
    assert_eq!(u30::from(UInt::<u32, 30>::new(0b10101)), u30::new(0b10101));
    assert_eq!(u30::from(UInt::<u64, 30>::new(0b10101)), u30::new(0b10101));
    assert_eq!(u30::from(UInt::<u128, 30>::new(0b10101)), u30::new(0b10101));

    assert_eq!(
        UInt::<u64, 7>::from(UInt::<u8, 7>::new(0b10101)),
        UInt::<u64, 7>::new(0b10101)
    );
    assert_eq!(
        UInt::<u64, 12>::from(UInt::<u16, 12>::new(0b10101)),
        UInt::<u64, 12>::new(0b10101)
    );
    assert_eq!(
        UInt::<u64, 28>::from(UInt::<u32, 28>::new(0b10101)),
        UInt::<u64, 28>::new(0b10101)
    );
    assert_eq!(u60::from(u60::new(0b10101)), u60::new(0b10101));
    assert_eq!(u60::from(UInt::<u128, 60>::new(0b10101)), u60::new(0b10101));

    assert_eq!(
        UInt::<u128, 5>::from(UInt::<u8, 5>::new(0b10101)),
        UInt::<u128, 5>::new(0b10101)
    );
    assert_eq!(
        UInt::<u128, 12>::from(UInt::<u16, 12>::new(0b10101)),
        UInt::<u128, 12>::new(0b10101)
    );
    assert_eq!(
        UInt::<u128, 26>::from(UInt::<u32, 26>::new(0b10101)),
        UInt::<u128, 26>::new(0b10101)
    );
    assert_eq!(
        UInt::<u128, 60>::from(UInt::<u64, 60>::new(0b10101)),
        UInt::<u128, 60>::new(0b10101)
    );
    assert_eq!(
        u120::from(UInt::<u128, 120>::new(0b10101)),
        u120::new(0b10101)
    );
}

#[cfg(feature = "num-traits")]
#[test]
fn calculation_with_number_trait() {
    fn increment_by_1<T: num_traits::WrappingAdd + Number>(foo: T) -> T {
        foo.wrapping_add(&T::new(1.into()))
    }

    fn increment_by_512<T: num_traits::WrappingAdd + Number>(
        foo: T,
    ) -> Result<T, <<T as Number>::UnderlyingType as TryFrom<u32>>::Error>
    where
        <<T as Number>::UnderlyingType as TryFrom<u32>>::Error: core::fmt::Debug,
    {
        Ok(foo.wrapping_add(&T::new(512u32.try_into()?)))
    }

    assert_eq!(increment_by_1(0u16), 1u16);
    assert_eq!(increment_by_1(u7::new(3)), u7::new(4));
    assert_eq!(increment_by_1(u15::new(3)), u15::new(4));

    assert_eq!(increment_by_512(0u16), Ok(512u16));
    assert!(increment_by_512(u7::new(3)).is_err());
    assert_eq!(increment_by_512(u15::new(3)), Ok(u15::new(515)));
}

#[test]
fn from_smaller_bit_widths() {
    // The code to get more bits from fewer bits (through From) is the same as the code above
    // for identical bitwidths. Therefore just do a few point checks to ensure things compile

    // There are compile-breakers for the opposite direction (e.g. tryint to do u5 = From(u17),
    // but we can't test compile failures here

    // from is not yet supported if the bitcounts are different but the base data types are the same (need
    // fancier Rust features to support that)
    assert_eq!(u6::from(UInt::<u16, 5>::new(0b10101)), u6::new(0b10101));
    assert_eq!(u6::from(UInt::<u32, 5>::new(0b10101)), u6::new(0b10101));
    assert_eq!(u6::from(UInt::<u64, 5>::new(0b10101)), u6::new(0b10101));
    assert_eq!(u6::from(UInt::<u128, 5>::new(0b10101)), u6::new(0b10101));

    assert_eq!(u15::from(UInt::<u8, 7>::new(0b10101)), u15::new(0b10101));
    //assert_eq!(u15::from(UInt::<u16, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u32, 14>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u64, 14>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u128, 14>::new(0b10101)), u15::new(0b10101));
}

#[allow(non_camel_case_types)]
#[test]
fn from_native_ints_same_bits() {
    use std::primitive;

    type u8 = UInt<primitive::u8, 8>;
    type u16 = UInt<primitive::u16, 16>;
    type u32 = UInt<primitive::u32, 32>;
    type u64 = UInt<primitive::u64, 64>;
    type u128 = UInt<primitive::u128, 128>;

    assert_eq!(u8::from(0x80_u8), u8::new(0x80));
    assert_eq!(u16::from(0x8000_u16), u16::new(0x8000));
    assert_eq!(u32::from(0x8000_0000_u32), u32::new(0x8000_0000));
    assert_eq!(
        u64::from(0x8000_0000_0000_0000_u64),
        u64::new(0x8000_0000_0000_0000)
    );
    assert_eq!(
        u128::from(0x8000_0000_0000_0000_0000_0000_0000_0000_u128),
        u128::new(0x8000_0000_0000_0000_0000_0000_0000_0000)
    );
}

#[test]
fn from_native_ints_fewer_bits() {
    assert_eq!(u9::from(0x80_u8), u9::new(0x80));

    assert_eq!(u17::from(0x80_u8), u17::new(0x80));
    assert_eq!(u17::from(0x8000_u16), u17::new(0x8000));

    assert_eq!(u33::from(0x80_u8), u33::new(0x80));
    assert_eq!(u33::from(0x8000_u16), u33::new(0x8000));
    assert_eq!(u33::from(0x8000_0000_u32), u33::new(0x8000_0000));

    assert_eq!(u65::from(0x80_u8), u65::new(0x80));
    assert_eq!(u65::from(0x8000_u16), u65::new(0x8000));
    assert_eq!(u65::from(0x8000_0000_u32), u65::new(0x8000_0000));
    assert_eq!(
        u65::from(0x8000_0000_0000_0000_u64),
        u65::new(0x8000_0000_0000_0000)
    );
}

#[allow(non_camel_case_types)]
#[test]
fn into_native_ints_same_bits() {
    assert_eq!(u8::from(UInt::<u8, 8>::new(0x80)), 0x80);
    assert_eq!(u16::from(UInt::<u16, 16>::new(0x8000)), 0x8000);
    assert_eq!(u32::from(UInt::<u32, 32>::new(0x8000_0000)), 0x8000_0000);
    assert_eq!(
        u64::from(UInt::<u64, 64>::new(0x8000_0000_0000_0000)),
        0x8000_0000_0000_0000
    );
    assert_eq!(
        u128::from(UInt::<u128, 128>::new(
            0x8000_0000_0000_0000_0000_0000_0000_0000
        )),
        0x8000_0000_0000_0000_0000_0000_0000_0000
    );
}

#[test]
fn into_native_ints_fewer_bits() {
    assert_eq!(u8::from(u7::new(0x40)), 0x40);
    assert_eq!(u16::from(u15::new(0x4000)), 0x4000);
    assert_eq!(u32::from(u31::new(0x4000_0000)), 0x4000_0000);
    assert_eq!(
        u64::from(u63::new(0x4000_0000_0000_0000)),
        0x4000_0000_0000_0000
    );
    assert_eq!(
        u128::from(u127::new(0x4000_0000_0000_0000_0000_0000_0000_0000)),
        0x4000_0000_0000_0000_0000_0000_0000_0000
    );
}

#[test]
fn from_into_bool() {
    assert_eq!(u1::from(true), u1::new(1));
    assert_eq!(u1::from(false), u1::new(0));
    assert_eq!(bool::from(u1::new(1)), true);
    assert_eq!(bool::from(u1::new(0)), false);
}

#[test]
fn widen() {
    // As From() can't be used while keeping the base-data-type, there's widen

    assert_eq!(u5::new(0b11011).widen::<6>(), u6::new(0b11011));
    assert_eq!(u5::new(0b11011).widen::<8>(), UInt::<u8, 8>::new(0b11011));
    assert_eq!(u10::new(0b11011).widen::<11>(), u11::new(0b11011));
    assert_eq!(u20::new(0b11011).widen::<24>(), u24::new(0b11011));
    assert_eq!(u60::new(0b11011).widen::<61>(), u61::new(0b11011));
    assert_eq!(u80::new(0b11011).widen::<127>().value(), 0b11011);
}

#[test]
fn to_string() {
    assert_eq!("Value: 5", format!("Value: {}", 5u32.to_string()));
    assert_eq!("Value: 5", format!("Value: {}", u5::new(5).to_string()));
    assert_eq!("Value: 5", format!("Value: {}", u11::new(5).to_string()));
    assert_eq!("Value: 5", format!("Value: {}", u17::new(5).to_string()));
    assert_eq!("Value: 5", format!("Value: {}", u38::new(5).to_string()));
    assert_eq!("Value: 60", format!("Value: {}", u65::new(60).to_string()));
}

#[test]
fn display() {
    assert_eq!("Value: 5", format!("Value: {}", 5u32));
    assert_eq!("Value: 5", format!("Value: {}", u5::new(5)));
    assert_eq!("Value: 5", format!("Value: {}", u11::new(5)));
    assert_eq!("Value: 5", format!("Value: {}", u17::new(5)));
    assert_eq!("Value: 5", format!("Value: {}", u38::new(5)));
    assert_eq!("Value: 60", format!("Value: {}", u65::new(60)));
}

#[test]
fn debug() {
    assert_eq!("Value: 5", format!("Value: {:?}", 5u32));
    assert_eq!("Value: 5", format!("Value: {:?}", u5::new(5)));
    assert_eq!("Value: 5", format!("Value: {:?}", u11::new(5)));
    assert_eq!("Value: 5", format!("Value: {:?}", u17::new(5)));
    assert_eq!("Value: 5", format!("Value: {:?}", u38::new(5)));
    assert_eq!("Value: 60", format!("Value: {:?}", u65::new(60)));
}

#[test]
fn lower_hex() {
    assert_eq!("Value: a", format!("Value: {:x}", 10u32));
    assert_eq!("Value: a", format!("Value: {:x}", u5::new(10)));
    assert_eq!("Value: a", format!("Value: {:x}", u11::new(10)));
    assert_eq!("Value: a", format!("Value: {:x}", u17::new(10)));
    assert_eq!("Value: a", format!("Value: {:x}", u38::new(10)));
    assert_eq!("Value: 3c", format!("Value: {:x}", 60));
    assert_eq!("Value: 3c", format!("Value: {:x}", u65::new(60)));
}

#[test]
fn upper_hex() {
    assert_eq!("Value: A", format!("Value: {:X}", 10u32));
    assert_eq!("Value: A", format!("Value: {:X}", u5::new(10)));
    assert_eq!("Value: A", format!("Value: {:X}", u11::new(10)));
    assert_eq!("Value: A", format!("Value: {:X}", u17::new(10)));
    assert_eq!("Value: A", format!("Value: {:X}", u38::new(10)));
    assert_eq!("Value: 3C", format!("Value: {:X}", 60));
    assert_eq!("Value: 3C", format!("Value: {:X}", u65::new(60)));
}

#[test]
fn lower_hex_fancy() {
    assert_eq!("Value: 0xa", format!("Value: {:#x}", 10u32));
    assert_eq!("Value: 0xa", format!("Value: {:#x}", u5::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x}", u11::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x}", u17::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x}", u38::new(10)));
    assert_eq!("Value: 0x3c", format!("Value: {:#x}", 60));
    assert_eq!("Value: 0x3c", format!("Value: {:#x}", u65::new(60)));
}

#[test]
fn upper_hex_fancy() {
    assert_eq!("Value: 0xA", format!("Value: {:#X}", 10u32));
    assert_eq!("Value: 0xA", format!("Value: {:#X}", u5::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X}", u11::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X}", u17::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X}", u38::new(10)));
    assert_eq!("Value: 0x3C", format!("Value: {:#X}", 60));
    assert_eq!("Value: 0x3C", format!("Value: {:#X}", u65::new(60)));
}

#[test]
fn debug_lower_hex_fancy() {
    assert_eq!("Value: 0xa", format!("Value: {:#x?}", 10u32));
    assert_eq!("Value: 0xa", format!("Value: {:#x?}", u5::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x?}", u11::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x?}", u17::new(10)));
    assert_eq!("Value: 0xa", format!("Value: {:#x?}", u38::new(10)));
    assert_eq!("Value: 0x3c", format!("Value: {:#x?}", 60));
    assert_eq!("Value: 0x3c", format!("Value: {:#x?}", u65::new(60)));
}

#[test]
fn debug_upper_hex_fancy() {
    assert_eq!("Value: 0xA", format!("Value: {:#X?}", 10u32));
    assert_eq!("Value: 0xA", format!("Value: {:#X?}", u5::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X?}", u11::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X?}", u17::new(10)));
    assert_eq!("Value: 0xA", format!("Value: {:#X?}", u38::new(10)));
    assert_eq!("Value: 0x3C", format!("Value: {:#X?}", 60));
    assert_eq!("Value: 0x3C", format!("Value: {:#X?}", u65::new(60)));
}

#[test]
fn octal() {
    assert_eq!("Value: 12", format!("Value: {:o}", 10u32));
    assert_eq!("Value: 12", format!("Value: {:o}", u5::new(10)));
    assert_eq!("Value: 12", format!("Value: {:o}", u11::new(10)));
    assert_eq!("Value: 12", format!("Value: {:o}", u17::new(10)));
    assert_eq!("Value: 12", format!("Value: {:o}", u38::new(10)));
    assert_eq!("Value: 74", format!("Value: {:o}", 0o74));
    assert_eq!("Value: 74", format!("Value: {:o}", u65::new(0o74)));
}

#[test]
fn binary() {
    assert_eq!("Value: 1010", format!("Value: {:b}", 10u32));
    assert_eq!("Value: 1010", format!("Value: {:b}", u5::new(10)));
    assert_eq!("Value: 1010", format!("Value: {:b}", u11::new(10)));
    assert_eq!("Value: 1010", format!("Value: {:b}", u17::new(10)));
    assert_eq!("Value: 1010", format!("Value: {:b}", u38::new(10)));
    assert_eq!("Value: 111100", format!("Value: {:b}", 0b111100));
    assert_eq!("Value: 111100", format!("Value: {:b}", u65::new(0b111100)));
}

#[test]
fn hash() {
    let mut hashmap = HashMap::<u5, u7>::new();

    hashmap.insert(u5::new(11), u7::new(9));

    assert_eq!(Some(&u7::new(9)), hashmap.get(&u5::new(11)));
    assert_eq!(None, hashmap.get(&u5::new(12)));
}

#[test]
fn swap_bytes() {
    assert_eq!(u24::new(0x12_34_56).swap_bytes(), u24::new(0x56_34_12));
    assert_eq!(
        UInt::<u64, 24>::new(0x12_34_56).swap_bytes(),
        UInt::<u64, 24>::new(0x56_34_12)
    );
    assert_eq!(
        UInt::<u128, 24>::new(0x12_34_56).swap_bytes(),
        UInt::<u128, 24>::new(0x56_34_12)
    );

    assert_eq!(
        u40::new(0x12_34_56_78_9A).swap_bytes(),
        u40::new(0x9A_78_56_34_12)
    );
    assert_eq!(
        UInt::<u128, 40>::new(0x12_34_56_78_9A).swap_bytes(),
        UInt::<u128, 40>::new(0x9A_78_56_34_12)
    );

    assert_eq!(
        u48::new(0x12_34_56_78_9A_BC).swap_bytes(),
        u48::new(0xBC_9A_78_56_34_12)
    );
    assert_eq!(
        UInt::<u128, 48>::new(0x12_34_56_78_9A_BC).swap_bytes(),
        UInt::<u128, 48>::new(0xBC_9A_78_56_34_12)
    );

    assert_eq!(
        u56::new(0x12_34_56_78_9A_BC_DE).swap_bytes(),
        u56::new(0xDE_BC_9A_78_56_34_12)
    );
    assert_eq!(
        UInt::<u128, 56>::new(0x12_34_56_78_9A_BC_DE).swap_bytes(),
        UInt::<u128, 56>::new(0xDE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u72::new(0x12_34_56_78_9A_BC_DE_FE_DC).swap_bytes(),
        u72::new(0xDC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u80::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA).swap_bytes(),
        u80::new(0xBA_DC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u88::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98).swap_bytes(),
        u88::new(0x98_BA_DC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u96::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76).swap_bytes(),
        u96::new(0x76_98_BA_DC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u104::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54).swap_bytes(),
        u104::new(0x54_76_98_BA_DC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u112::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32).swap_bytes(),
        u112::new(0x32_54_76_98_BA_DC_FE_DE_BC_9A_78_56_34_12)
    );

    assert_eq!(
        u120::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32_10).swap_bytes(),
        u120::new(0x10_32_54_76_98_BA_DC_FE_DE_BC_9A_78_56_34_12)
    );
}

#[test]
fn to_le_and_be_bytes() {
    assert_eq!(u24::new(0x12_34_56).to_le_bytes(), [0x56, 0x34, 0x12]);
    assert_eq!(
        UInt::<u64, 24>::new(0x12_34_56).to_le_bytes(),
        [0x56, 0x34, 0x12]
    );
    assert_eq!(
        UInt::<u128, 24>::new(0x12_34_56).to_le_bytes(),
        [0x56, 0x34, 0x12]
    );

    assert_eq!(u24::new(0x12_34_56).to_be_bytes(), [0x12, 0x34, 0x56]);
    assert_eq!(
        UInt::<u64, 24>::new(0x12_34_56).to_be_bytes(),
        [0x12, 0x34, 0x56]
    );
    assert_eq!(
        UInt::<u128, 24>::new(0x12_34_56).to_be_bytes(),
        [0x12, 0x34, 0x56]
    );

    assert_eq!(
        u40::new(0x12_34_56_78_9A).to_le_bytes(),
        [0x9A, 0x78, 0x56, 0x34, 0x12]
    );
    assert_eq!(
        UInt::<u128, 40>::new(0x12_34_56_78_9A).to_le_bytes(),
        [0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u40::new(0x12_34_56_78_9A).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A]
    );
    assert_eq!(
        UInt::<u128, 40>::new(0x12_34_56_78_9A).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A]
    );

    assert_eq!(
        u48::new(0x12_34_56_78_9A_BC).to_le_bytes(),
        [0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );
    assert_eq!(
        UInt::<u128, 48>::new(0x12_34_56_78_9A_BC).to_le_bytes(),
        [0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u48::new(0x12_34_56_78_9A_BC).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC]
    );
    assert_eq!(
        UInt::<u128, 48>::new(0x12_34_56_78_9A_BC).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC]
    );

    assert_eq!(
        u56::new(0x12_34_56_78_9A_BC_DE).to_le_bytes(),
        [0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );
    assert_eq!(
        UInt::<u128, 56>::new(0x12_34_56_78_9A_BC_DE).to_le_bytes(),
        [0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u56::new(0x12_34_56_78_9A_BC_DE).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE]
    );
    assert_eq!(
        UInt::<u128, 56>::new(0x12_34_56_78_9A_BC_DE).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE]
    );

    assert_eq!(
        u72::new(0x12_34_56_78_9A_BC_DE_FE_DC).to_le_bytes(),
        [0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u72::new(0x12_34_56_78_9A_BC_DE_FE_DC).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC]
    );

    assert_eq!(
        u80::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA).to_le_bytes(),
        [0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u80::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA]
    );

    assert_eq!(
        u88::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98).to_le_bytes(),
        [0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u88::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98]
    );

    assert_eq!(
        u96::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76).to_le_bytes(),
        [0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u96::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76]
    );

    assert_eq!(
        u104::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54).to_le_bytes(),
        [0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u104::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54]
    );

    assert_eq!(
        u112::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32).to_le_bytes(),
        [0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    assert_eq!(
        u112::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32).to_be_bytes(),
        [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32]
    );

    assert_eq!(
        u120::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32_10).to_le_bytes(),
        [
            0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34,
            0x12
        ]
    );

    assert_eq!(
        u120::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32_10).to_be_bytes(),
        [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32,
            0x10
        ]
    );
}

#[test]
fn from_le_and_be_bytes() {
    assert_eq!(u24::from_le_bytes([0x56, 0x34, 0x12]), u24::new(0x12_34_56));
    assert_eq!(
        UInt::<u64, 24>::from_le_bytes([0x56, 0x34, 0x12]),
        UInt::<u64, 24>::new(0x12_34_56)
    );
    assert_eq!(
        UInt::<u128, 24>::from_le_bytes([0x56, 0x34, 0x12]),
        UInt::<u128, 24>::new(0x12_34_56)
    );

    assert_eq!(u24::from_be_bytes([0x12, 0x34, 0x56]), u24::new(0x12_34_56));
    assert_eq!(
        UInt::<u64, 24>::from_be_bytes([0x12, 0x34, 0x56]),
        UInt::<u64, 24>::new(0x12_34_56)
    );
    assert_eq!(
        UInt::<u128, 24>::from_be_bytes([0x12, 0x34, 0x56]),
        UInt::<u128, 24>::new(0x12_34_56)
    );

    assert_eq!(
        u40::from_le_bytes([0x9A, 0x78, 0x56, 0x34, 0x12]),
        u40::new(0x12_34_56_78_9A)
    );
    assert_eq!(
        UInt::<u128, 40>::from_le_bytes([0x9A, 0x78, 0x56, 0x34, 0x12]),
        UInt::<u128, 40>::new(0x12_34_56_78_9A)
    );

    assert_eq!(
        u40::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A]),
        u40::new(0x12_34_56_78_9A)
    );
    assert_eq!(
        UInt::<u128, 40>::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A]),
        UInt::<u128, 40>::new(0x12_34_56_78_9A)
    );

    assert_eq!(
        u48::from_le_bytes([0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        u48::new(0x12_34_56_78_9A_BC)
    );
    assert_eq!(
        UInt::<u128, 48>::from_le_bytes([0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        UInt::<u128, 48>::new(0x12_34_56_78_9A_BC)
    );

    assert_eq!(
        u48::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC]),
        u48::new(0x12_34_56_78_9A_BC)
    );
    assert_eq!(
        UInt::<u128, 48>::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC]),
        UInt::<u128, 48>::new(0x12_34_56_78_9A_BC)
    );

    assert_eq!(
        u56::from_le_bytes([0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        u56::new(0x12_34_56_78_9A_BC_DE)
    );
    assert_eq!(
        UInt::<u128, 56>::from_le_bytes([0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        UInt::<u128, 56>::new(0x12_34_56_78_9A_BC_DE)
    );

    assert_eq!(
        u56::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE]),
        u56::new(0x12_34_56_78_9A_BC_DE)
    );
    assert_eq!(
        UInt::<u128, 56>::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE]),
        UInt::<u128, 56>::new(0x12_34_56_78_9A_BC_DE)
    );

    assert_eq!(
        u72::from_le_bytes([0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        u72::new(0x12_34_56_78_9A_BC_DE_FE_DC)
    );

    assert_eq!(
        u72::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC]),
        u72::new(0x12_34_56_78_9A_BC_DE_FE_DC)
    );

    assert_eq!(
        u80::from_le_bytes([0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        u80::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA)
    );

    assert_eq!(
        u80::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA]),
        u80::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA)
    );

    assert_eq!(
        u88::from_le_bytes([0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]),
        u88::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98)
    );

    assert_eq!(
        u88::from_be_bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98]),
        u88::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98)
    );

    assert_eq!(
        u96::from_le_bytes([
            0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12
        ]),
        u96::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76)
    );

    assert_eq!(
        u96::from_be_bytes([
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76
        ]),
        u96::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76)
    );

    assert_eq!(
        u104::from_le_bytes([
            0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12
        ]),
        u104::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54)
    );

    assert_eq!(
        u104::from_be_bytes([
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54
        ]),
        u104::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54)
    );

    assert_eq!(
        u112::from_le_bytes([
            0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12
        ]),
        u112::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32)
    );

    assert_eq!(
        u112::from_be_bytes([
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32
        ]),
        u112::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32)
    );

    assert_eq!(
        u120::from_le_bytes([
            0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34,
            0x12
        ]),
        u120::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32_10)
    );

    assert_eq!(
        u120::from_be_bytes([
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32,
            0x10
        ]),
        u120::new(0x12_34_56_78_9A_BC_DE_FE_DC_BA_98_76_54_32_10)
    );
}

#[test]
fn to_ne_bytes() {
    if cfg!(target_endian = "little") {
        assert_eq!(
            u40::new(0x12_34_56_78_9A).to_ne_bytes(),
            [0x9A, 0x78, 0x56, 0x34, 0x12]
        );
    } else {
        assert_eq!(
            u40::new(0x12_34_56_78_9A).to_ne_bytes(),
            [0x12, 0x34, 0x56, 0x78, 0x9A]
        );
    }
}

#[test]
fn from_ne_bytes() {
    if cfg!(target_endian = "little") {
        assert_eq!(
            u40::from_ne_bytes([0x9A, 0x78, 0x56, 0x34, 0x12]),
            u40::new(0x12_34_56_78_9A)
        );
    } else {
        assert_eq!(
            u40::from_ne_bytes([0x12, 0x34, 0x56, 0x78, 0x9A]),
            u40::new(0x12_34_56_78_9A)
        );
    }
}

#[test]
fn simple_le_be() {
    const REGULAR: u40 = u40::new(0x12_34_56_78_9A);
    const SWAPPED: u40 = u40::new(0x9A_78_56_34_12);
    if cfg!(target_endian = "little") {
        assert_eq!(REGULAR.to_le(), REGULAR);
        assert_eq!(REGULAR.to_be(), SWAPPED);
        assert_eq!(u40::from_le(REGULAR), REGULAR);
        assert_eq!(u40::from_be(REGULAR), SWAPPED);
    } else {
        assert_eq!(REGULAR.to_le(), SWAPPED);
        assert_eq!(REGULAR.to_be(), REGULAR);
        assert_eq!(u40::from_le(REGULAR), SWAPPED);
        assert_eq!(u40::from_be(REGULAR), REGULAR);
    }
}

#[test]
fn reverse_bits() {
    const A: u5 = u5::new(0b11101);
    const B: u5 = A.reverse_bits();
    assert_eq!(B, u5::new(0b10111));

    assert_eq!(
        UInt::<u128, 6>::new(0b101011),
        UInt::<u128, 6>::new(0b110101).reverse_bits()
    );

    assert_eq!(u1::new(1).reverse_bits().value(), 1);
    assert_eq!(u1::new(0).reverse_bits().value(), 0);
}

#[test]
fn count_ones_and_zeros() {
    assert_eq!(4, u5::new(0b10111).count_ones());
    assert_eq!(1, u5::new(0b10111).count_zeros());
    assert_eq!(1, u5::new(0b10111).leading_ones());
    assert_eq!(0, u5::new(0b10111).leading_zeros());
    assert_eq!(3, u5::new(0b10111).trailing_ones());
    assert_eq!(0, u5::new(0b10111).trailing_zeros());

    assert_eq!(2, u5::new(0b10100).trailing_zeros());
    assert_eq!(3, u5::new(0b00011).leading_zeros());

    assert_eq!(0, u5::new(0b00000).count_ones());
    assert_eq!(5, u5::new(0b00000).count_zeros());

    assert_eq!(5, u5::new(0b11111).count_ones());
    assert_eq!(0, u5::new(0b11111).count_zeros());

    assert_eq!(3, u127::new(0b111).count_ones());
    assert_eq!(124, u127::new(0b111).count_zeros());
}

#[test]
fn rotate_left() {
    assert_eq!(u1::new(0b1), u1::new(0b1).rotate_left(1));
    assert_eq!(u2::new(0b01), u2::new(0b10).rotate_left(1));

    assert_eq!(u5::new(0b10111), u5::new(0b10111).rotate_left(0));
    assert_eq!(u5::new(0b01111), u5::new(0b10111).rotate_left(1));
    assert_eq!(u5::new(0b11110), u5::new(0b10111).rotate_left(2));
    assert_eq!(u5::new(0b11101), u5::new(0b10111).rotate_left(3));
    assert_eq!(u5::new(0b11011), u5::new(0b10111).rotate_left(4));
    assert_eq!(u5::new(0b10111), u5::new(0b10111).rotate_left(5));
    assert_eq!(u5::new(0b01111), u5::new(0b10111).rotate_left(6));
    assert_eq!(u5::new(0b01111), u5::new(0b10111).rotate_left(556));

    assert_eq!(u24::new(0x0FFEEC), u24::new(0xC0FFEE).rotate_left(4));
}

#[test]
fn rotate_right() {
    assert_eq!(u1::new(0b1), u1::new(0b1).rotate_right(1));
    assert_eq!(u2::new(0b01), u2::new(0b10).rotate_right(1));

    assert_eq!(u5::new(0b10011), u5::new(0b10011).rotate_right(0));
    assert_eq!(u5::new(0b11001), u5::new(0b10011).rotate_right(1));
    assert_eq!(u5::new(0b11100), u5::new(0b10011).rotate_right(2));
    assert_eq!(u5::new(0b01110), u5::new(0b10011).rotate_right(3));
    assert_eq!(u5::new(0b00111), u5::new(0b10011).rotate_right(4));
    assert_eq!(u5::new(0b10011), u5::new(0b10011).rotate_right(5));
    assert_eq!(u5::new(0b11001), u5::new(0b10011).rotate_right(6));

    assert_eq!(u24::new(0xEC0FFE), u24::new(0xC0FFEE).rotate_right(4));
}

#[cfg(feature = "step_trait")]
#[test]
fn range_agrees_with_underlying() {
    compare_range(u19::MIN, u19::MAX);
    compare_range(u37::new(95_993), u37::new(1_994_910));
    compare_range(u68::new(58_858_348), u68::new(58_860_000));
    compare_range(u122::new(111_222_333_444), u122::new(111_222_444_555));
    compare_range(u5::MIN, u5::MAX);
    compare_range(u23::MIN, u23::MAX);
    compare_range(u48::new(999_444), u48::new(1_005_000));
    compare_range(u99::new(12345), u99::new(54321));

    fn compare_range<T, const BITS: usize>(arb_start: UInt<T, BITS>, arb_end: UInt<T, BITS>)
    where
        T: Copy + Step,
        UInt<T, BITS>: Step,
    {
        let arbint_range = (arb_start..=arb_end).map(UInt::value);
        let underlying_range = arb_start.value()..=arb_end.value();

        assert!(arbint_range.eq(underlying_range));
    }
}

#[cfg(feature = "step_trait")]
#[test]
fn forward_checked() {
    // In range
    assert_eq!(Some(u7::new(121)), Step::forward_checked(u7::new(120), 1));
    assert_eq!(Some(u7::new(127)), Step::forward_checked(u7::new(120), 7));

    // Out of range
    assert_eq!(None, Step::forward_checked(u7::new(120), 8));

    // Out of range for the underlying type
    assert_eq!(None, Step::forward_checked(u7::new(120), 140));
}

#[cfg(feature = "step_trait")]
#[test]
fn backward_checked() {
    // In range
    assert_eq!(Some(u7::new(1)), Step::backward_checked(u7::new(10), 9));
    assert_eq!(Some(u7::new(0)), Step::backward_checked(u7::new(10), 10));

    // Out of range (for both the arbitrary int and and the underlying type)
    assert_eq!(None, Step::backward_checked(u7::new(10), 11));
}

#[cfg(feature = "step_trait")]
#[test]
fn steps_between() {
    assert_eq!(Some(0), Step::steps_between(&u50::new(50), &u50::new(50)));

    assert_eq!(Some(4), Step::steps_between(&u24::new(5), &u24::new(9)));
    assert_eq!(None, Step::steps_between(&u24::new(9), &u24::new(5)));

    // this assumes usize is <= 64 bits. a test like this one exists in `core::iter::step`.
    assert_eq!(
        Some(usize::MAX),
        Step::steps_between(&u125::new(0x7), &u125::new(0x1_0000_0000_0000_0006))
    );
    assert_eq!(
        None,
        Step::steps_between(&u125::new(0x7), &u125::new(0x1_0000_0000_0000_0007))
    );
}
