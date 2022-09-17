Unreleased
----------
- Bumped required Rust version to `1.46`


0.2.5
-----
- Introduced `Num32` and `Num64` types with fixed size and limited
  precision
- Added support for converting number types into a pair of their
  components


0.2.4
-----
- Added `num-v04` feature for using `num-*` crates in version `0.4`
  - Added `num-v02` (enabled by default) for `0.2` variants
- Added re-exports of `num_bigint` and `num_rational` crates
- Excluded unnecessary files from being contained in release bundle


0.2.3
-----
- Added efficient serialization & deserialization support for non
  self-describing formats such as `bincode`


0.2.2
-----
- Added support for converting a `Num` into a floating point number
- Enabled CI pipeline comprising building, testing, linting, and
  coverage collection of the project
  - Added badges indicating pipeline status and code coverage percentage
- Bumped required Rust version to `1.43`


0.2.1
-----
- Added support for printing a `Num` with a minimum precision
- Added export for `ParseNumError` error type


0.2.0
-----
- Added `From` implementations for various integer types
  - Removed `Num::from_int` constructor
- Adjusted `Num::new` constructor to work with various integer types


0.1.0
-----
- Initial release
