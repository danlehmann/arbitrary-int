# Changelog

## arbitrary-int 1.2.7

### Added

- Support `Step` so that arbitrary-int can be used in a range expression, e.g. `for n in u3::MIN..=u3::MAX { println!("{n}") }`. Note this trait is currently unstable, and so is only usable in nightly. Enable this feature with `step_trait`.
- Support formatting via [defmt](https://crates.io/crates/defmt). Enable the option `defmt` feature
- Support serializing and deserializing via [serde](https://crates.io/crates/serde). Enable the option `serde` feature
- Implement `Mul`, `MulAssign`, `Div`, `DivAssign`
- Implement `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_div`, `wrapping_shl`, `wrapping_shr`
- Implement `saturating_add`, `saturating_sub`, `saturating_mul`, `saturating_div`, `saturating_pow`

### Changed
- In debug builds, `<<` (`Shl`, `ShlAssign`) and `>>` (`Shr`, `ShrAssign`) now bounds-check the shift amount using the same semantics as built-in shifts. For example, shifting a u5 by 5 or more bits will now panic as expected.

## arbitrary-int 1.2.6

### Added

- Support `LowerHex`, `UpperHex`, `Octal`, `Binary` so that arbitrary-int can be printed via e.g. `format!("{:x}", u4::new(12))`
- Support `Hash` so that arbitrary-int can be used in hash tables

### Changed

- As support for `[const_trait]` has recently been removed from structs like `From<T>` in upstream Rust, opting-in to the `nightly` feature no longer enables this behavior as that would break the build. To continue using this feature with older compiler versions, use `const_convert_and_const_trait_impl` instead.

## arbitrary-int 1.2.5

### Added

- Types that can be expressed as full bytes (e.g. u24, u48) have the following new methods:
    * `swap_bytes()`
    * `to_le_bytes()`
    * `to_be_bytes()`
    * `to_ne_bytes()`
    * `to_be()`
    * `to_le()`

### Changed

- `#[inline]` is specified in more places

### Fixed
