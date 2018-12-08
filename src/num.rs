// Copyright (C) 2019 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::error::Error as StdError;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::num::ParseIntError;
use std::str::FromStr;

use num_bigint::BigInt;
use num_bigint::Sign;
use num_rational::BigRational;


/// An error used for conveying parsing failures.
#[derive(Debug)]
pub enum ParseNumError {
  /// A string could not get parsed as a `Num`.
  InvalidStrError(String),
  /// An integer value could not get parsed.
  ParseIntError(ParseIntError),
}

impl From<ParseIntError> for ParseNumError {
  fn from(e: ParseIntError) -> Self {
    Self::ParseIntError(e)
  }
}

impl Display for ParseNumError {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    match self {
      Self::InvalidStrError(s) => write!(fmt, "{}", s),
      Self::ParseIntError(err) => write!(fmt, "{}", err),
    }
  }
}

impl StdError for ParseNumError {}


/// An unlimited precision number type with some improvements and
/// customizations over `BigRational`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Num(BigRational);

impl Num {
  /// Construct a `Num` from two integers.
  pub fn new(numer: u32, denom: u32) -> Self {
    let numer = BigInt::from_slice(Sign::Plus, &[numer.to_le()]);
    let denom = BigInt::from_slice(Sign::Plus, &[denom.to_le()]);
    Num(BigRational::new(numer, denom))
  }

  /// Construct a `Num` from an integer.
  pub fn from_int(val: u32) -> Self {
    Num(BigRational::from_integer(BigInt::from_slice(
      Sign::Plus,
      &[val.to_le()],
    )))
  }
}

impl Display for Num {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    // TODO: We probably want to format this value as a float.
    write!(fmt, "{}", self.0)
  }
}

impl FromStr for Num {
  type Err = ParseNumError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    fn parse_str(s: &str) -> Result<BigInt, ParseNumError> {
      let num = u32::from_str(s)?;
      let num = BigInt::from_slice(Sign::Plus, &[num.to_le()]);
      Ok(num)
    }

    let mut splits = s.splitn(2, '.');
    let numer = splits
      .next()
      .ok_or_else(|| ParseNumError::InvalidStrError(s.to_owned()))?;
    let numer = parse_str(numer)?;

    if let Some(s) = splits.next() {
      let denom = parse_str(s)?;
      // TODO: Should use checked_pow once it is stable.
      let power = 10u32.pow(s.len() as u32);
      let power = BigInt::from_slice(Sign::Plus, &[power.to_le()]);
      let numer = numer * &power + denom;
      Ok(Num(BigRational::new(numer, power)))
    } else {
      Ok(Num(BigRational::from_integer(numer)))
    }
  }
}


#[cfg(test)]
mod tests {
  use super::*;


  #[test]
  fn num_from_int() {
    let num = Num::from_str("42").unwrap();
    assert_eq!(num, Num::from_int(42));
  }

  #[test]
  fn num_from_float() {
    let num = Num::from_str("4000.32").unwrap();
    assert_eq!(num, Num::new(400032, 100));
  }
}
