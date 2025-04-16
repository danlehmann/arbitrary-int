use crate::UnsignedInteger;

/// Compatibility with arbitrary-int 1.x, which didn't support signed integers.
///
/// Going forward, use [`UnsignedInteger`] (to allow only unsigned integers) or [`Integer`] (to
/// support either signed or unsigned)
#[deprecated(since = "2.0", note = "Use [`UnsignedInteger`] or [`Integer`] instead")]
#[cfg_attr(feature = "const_convert_and_const_trait_impl", const_trait)]
pub trait Number: UnsignedInteger {}
