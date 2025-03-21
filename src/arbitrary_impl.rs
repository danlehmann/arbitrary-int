use ::arbitrary::{Arbitrary, Unstructured, Result, unstructured};

use super::*;

impl<'a, T, const BITS: usize> Arbitrary<'a> for UInt<T, BITS>
where
  T: unstructured::Int,
  Self: Number<UnderlyingType = T>,
{
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    u.int_in_range(Self::MIN.value()..=Self::MAX.value())
      .map(Self::new)
  }
}

impl<'a, T, const BITS: usize> Arbitrary<'a> for Int<T, BITS>
where
  T: unstructured::Int,
  Self: SignedNumber<UnderlyingType = T>,
{
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    u.int_in_range(Self::MIN.value()..=Self::MAX.value())
      .map(Self::new)
  }
}

#[allow(dead_code)]
const fn static_assertion<'a, T>()
where
  T: Arbitrary<'a>,
{}

macro_rules! check {
  ($($lit:ident), +$(,)?) => {
    $(
      const _: () = static_assertion::<'_, $lit>();
    )*
  };
}

macro_rules! check_bunch {
  ($($start:literal..=$end:literal), +$(,)?) => {
    $(
      seq_macro::seq!(N in $start..=$end {
        check!(#(u~N,)*);
      });
      
      seq_macro::seq!(N in $start..=$end {
        check!(#(i~N,)*);
      });
    )*
  };
}

check_bunch!(
  1..=7,
  9..=15,
  17..=31,
  33..=63,
  65..=127,
);

