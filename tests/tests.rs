extern crate core;

use arbitrary_int::{u10, u11, u120, u127, u13, u14, u15, u17, u20, u23, u24, u30, u31, u4, u5, u6, u60, u61, u63, u67, u7, u80, u9, UInt};

#[test]
fn create_simple() {
    let value7 = u7::new(123);
    let value13 = u13::new(123);
    let value23 = u23::new(123);
    let value67 = u67::new(123);

    assert_eq!(value7.value(), 123);
    assert_eq!(value13.value(), 123);
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
    let _ = u7::new(127) + u7::new(1);
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
    assert_eq!(u17::new(0b11001100) & u17::new(0b01101001), u17::new(0b01001000));
    assert_eq!(u17::new(0b11001100) & u17::new(0), u17::new(0));
    assert_eq!(u17::new(0b11001100) & u17::new(0x1_FFFF), u17::new(0b11001100));
}

#[test]
fn bitandassign() {
    let mut value = u4::new(0b0101);
    value &= u4::new(0b0110);
    assert_eq!(value, u4::new(0b0100));
}

#[test]
fn bitor() {
    assert_eq!(u17::new(0b11001100) | u17::new(0b01101001), u17::new(0b11101101));
    assert_eq!(u17::new(0b11001100) | u17::new(0), u17::new(0b11001100));
    assert_eq!(u17::new(0b11001100) | u17::new(0x1_FFFF), u17::new(0x1_FFFF));
}

#[test]
fn bitorassign() {
    let mut value = u4::new(0b0101);
    value |= u4::new(0b0110);
    assert_eq!(value, u4::new(0b0111));
}

#[test]
fn bitxor() {
    assert_eq!(u17::new(0b11001100) ^ u17::new(0b01101001), u17::new(0b10100101));
    assert_eq!(u17::new(0b11001100) ^ u17::new(0), u17::new(0b11001100));
    assert_eq!(u17::new(0b11001100) ^ u17::new(0x1_FFFF), u17::new(0b1_11111111_00110011));
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

    assert_eq!(0, u15::MIN.value());
    assert_eq!(32767, u15::MAX.value());

    assert_eq!(0, u31::MIN.value());
    assert_eq!(2147483647, u31::MAX.value());

    assert_eq!(0, u63::MIN.value());
    assert_eq!(0x7FFF_FFFF_FFFF_FFFF, u63::MAX.value());

    assert_eq!(0, u127::MIN.value());
    assert_eq!(0x7FFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, u127::MAX.value());
}

#[test]
fn extract() {
    assert_eq!(u5::new(0b10000), u5::extract(0b11110000, 0));
    assert_eq!(u5::new(0b11100), u5::extract(0b11110000, 2));
    assert_eq!(u5::new(0b11110), u5::extract(0b11110000, 3));

    // Use extract with a custom type (5 bits of u32)
    assert_eq!(UInt::<u32, 5>::new(0b11110), UInt::<u32, 5>::extract(0b11110000, 3));
}

#[test]
#[should_panic]
fn extract_not_enough_bits() {
    let _ = u5::extract(0b11110000, 4);
}

#[test]
fn from_same_bit_widths() {
    assert_eq!(u5::from(UInt::<u8, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u16, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u32, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u64, 5>::new(0b10101)), u5::new(0b10101));
    assert_eq!(u5::from(UInt::<u128, 5>::new(0b10101)), u5::new(0b10101));

    assert_eq!(UInt::<u16, 6>::from(UInt::<u8, 5>::new(0b10101)), UInt::<u16, 6>::new(0b10101));
    assert_eq!(u15::from(UInt::<u16, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u32, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u64, 15>::new(0b10101)), u15::new(0b10101));
    assert_eq!(u15::from(UInt::<u128, 15>::new(0b10101)), u15::new(0b10101));

    assert_eq!(UInt::<u32, 6>::from(u6::new(0b10101)), UInt::<u32, 6>::new(0b10101));
    assert_eq!(UInt::<u32, 14>::from(u14::new(0b10101)), UInt::<u32, 14>::new(0b10101));
    assert_eq!(u30::from(UInt::<u32, 30>::new(0b10101)), u30::new(0b10101));
    assert_eq!(u30::from(UInt::<u64, 30>::new(0b10101)), u30::new(0b10101));
    assert_eq!(u30::from(UInt::<u128, 30>::new(0b10101)), u30::new(0b10101));

    assert_eq!(UInt::<u64, 7>::from(UInt::<u8, 7>::new(0b10101)), UInt::<u64, 7>::new(0b10101));
    assert_eq!(UInt::<u64, 12>::from(UInt::<u16, 12>::new(0b10101)), UInt::<u64, 12>::new(0b10101));
    assert_eq!(UInt::<u64, 28>::from(UInt::<u32, 28>::new(0b10101)), UInt::<u64, 28>::new(0b10101));
    assert_eq!(u60::from(u60::new(0b10101)), u60::new(0b10101));
    assert_eq!(u60::from(UInt::<u128, 60>::new(0b10101)), u60::new(0b10101));

    assert_eq!(UInt::<u128, 5>::from(UInt::<u8, 5>::new(0b10101)), UInt::<u128, 5>::new(0b10101));
    assert_eq!(UInt::<u128, 12>::from(UInt::<u16, 12>::new(0b10101)), UInt::<u128, 12>::new(0b10101));
    assert_eq!(UInt::<u128, 26>::from(UInt::<u32, 26>::new(0b10101)), UInt::<u128, 26>::new(0b10101));
    assert_eq!(UInt::<u128, 60>::from(UInt::<u64, 60>::new(0b10101)), UInt::<u128, 60>::new(0b10101));
    assert_eq!(u120::from(UInt::<u128, 120>::new(0b10101)), u120::new(0b10101));
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

#[test]
fn widen() {
    // As From() can't be used while keeping the base-data-type, there's widen

    assert_eq!(u5::new(0b11011).widen::<6>(), u6::new(0b11011));
    assert_eq!(u10::new(0b11011).widen::<11>(), u11::new(0b11011));
    assert_eq!(u20::new(0b11011).widen::<24>(), u24::new(0b11011));
    assert_eq!(u60::new(0b11011).widen::<61>(), u61::new(0b11011));
    assert_eq!(u80::new(0b11011).widen::<127>().value(), 0b11011);
}
