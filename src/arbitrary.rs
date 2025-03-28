use ::arbitrary::{unstructured, Arbitrary, Result, Unstructured};

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
