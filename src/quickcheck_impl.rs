use ::quickcheck::{Arbitrary, Gen};

use super::*;

impl<T, const BITS: usize> Arbitrary for UInt<T, BITS>
where
  T: Arbitrary,
  Self: Number<UnderlyingType = T>,
{
  fn arbitrary(g: &mut Gen) -> Self {
    loop {
      match Self::try_new(T::arbitrary(g)) {
        Ok(value) => break value,
        Err(_) => continue,
      }
    }
  }
}

impl<T, const BITS: usize> Arbitrary for Int<T, BITS>
where
  T: Arbitrary,
  Self: SignedNumber<UnderlyingType = T>,
{
  fn arbitrary(g: &mut Gen) -> Self {
    loop {
      match Self::try_new(T::arbitrary(g)) {
        Ok(value) => break value,
        Err(_) => continue,
      }
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use quickcheck_macros::quickcheck;

  macro_rules! gen_quickcheck_tests {
    ($($lit:ident), +$(,)?) => {
      paste::paste! {
        $(
          #[quickcheck]
          fn [< quickcheck_ $lit >](_: $lit) -> bool {
            true
          }
        )*
      }
    };
  }

  macro_rules! quickcheck_gen {
    ($($start:literal..=$end:literal), +$(,)?) => {
      $(
        seq_macro::seq!(N in $start..=$end {
          gen_quickcheck_tests!(#(u~N,)*);
        });
        
        seq_macro::seq!(N in $start..=$end {
          gen_quickcheck_tests!(#(i~N,)*);
        });
      )*
    };
  }

  quickcheck_gen!(
    1..=7,
    9..=15,
    17..=31,
    33..=63,
    65..=127,
  );
}