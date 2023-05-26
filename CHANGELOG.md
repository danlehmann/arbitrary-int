# Changelog

## arbitrary-int 1.2.6

### Added

- Support LowerHex and UpperHex so that arbitrary-int can be printed via e.g. `format!("{:x}", u4::new(12))`

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