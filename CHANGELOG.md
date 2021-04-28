Unreleased
----------
- Excluded unnecessary files from being contained in release bundle


0.2.3
-----
- Added efficient serialization & deserializtion support for non
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
