//!```compile_fail,E0080
//! #![cfg(not(feature = "const_convert_and_const_trait_impl"))]
//! use arbitrary_int::u48;
//! let _ = u48!(9_223_372_036_854_775_807u64); // error: literal out of range for `u48`
//!```
