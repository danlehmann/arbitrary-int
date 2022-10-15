extern crate core;

use arbitrary_int::*;

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

#[test]
#[should_panic]
fn add_overflow() {
    let _ = u7::new(127) + u7::new(3);
}

#[test]
fn num_traits_add_wrapping() {
    let v1 = u7::new(120);
    let v2 = u7::new(10);
    let v3 = num_traits::WrappingAdd::wrapping_add(&v1, &v2);
    assert_eq!(v3, u7::new(2));
}

#[test]
fn num_traits_sub_wrapping() {
    let v1 = u7::new(15);
    let v2 = u7::new(20);
    let v3 = num_traits::WrappingSub::wrapping_sub(&v1, &v2);
    assert_eq!(v3, u7::new(123));
}

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

#[test]
#[should_panic]
fn addassign_overflow() {
    let mut value = u9::new(500);
    value += u9::new(40);
}

#[test]
fn sub() {
    assert_eq!(u7::new(22) - u7::new(10), u7::new(12));
    assert_eq!(u7::new(127) - u7::new(127), u7::new(0));
}

#[test]
#[should_panic]
fn sub_overflow() {
    let _ = u7::new(100) - u7::new(127);
}

#[test]
fn subassign() {
    let mut value = u9::new(500);
    value -= u9::new(11);
    assert_eq!(value, u9::new(489));
}

#[test]
#[should_panic]
fn subassign_overflow() {
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
    assert_eq!(0b1010_0011, UInt::<u8, 8>::extract_u8(0b1010_0011, 0).value());
    assert_eq!(0b1010_0011, UInt::<u8, 8>::extract_u16(0b1111_1111_1010_0011, 0).value());
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

    assert_eq!(UInt::<u8, 8>::from(UInt::<u128, 8>::new(0b1110_0101)), UInt::<u8, 8>::new(0b1110_0101));

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
