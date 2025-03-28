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
