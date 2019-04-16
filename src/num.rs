// Copyright (C) 2019 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::error::Error as StdError;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::i32;
use std::num::ParseIntError;
use std::str::FromStr;

use serde::de::Error;
use serde::de::Unexpected;
use serde::Deserialize;
use serde::Deserializer;

use num_bigint::BigInt;
use num_bigint::Sign;
use num_rational::BigRational;
use num_traits::sign::Signed;


/// Round the given `BigRational` to the nearest integer. Rounding
/// happens based on the Round-Half-To-Even scheme (also known as the
/// "banker's rounding" algorithm), which rounds to the closest integer
/// as expected but if the fractional part is exactly 1/2 (i.e.,
/// equidistant from two integers) it rounds to the even one of the two.
fn round_to_even(val: &BigRational) -> BigRational {
  let zero = new_bigint(0);
  let one = new_bigint(1);
  let two = new_bigint(2);

  let zero_ = BigRational::new(zero.clone(), one.clone());
  let half = BigRational::new(one.clone(), two.clone());
  // Find unsigned fractional part of rational number.
  let mut fract = val.fract();
  if fract < zero_ {
    fract = &zero_ - fract
  };

  let trunc = val.trunc();
  if fract == half {
    // If the denominator is even round down, otherwise round up.
    if &trunc % two == zero_ {
      trunc
    } else if trunc >= zero_ {
      trunc + one
    } else {
      trunc - one
    }
  } else {
    // BigRational::round() behaves as we want it for all cases except
    // where the fractional part is 1/2.
    val.round()
  }
}


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


/// Create a `BigInt` from an `i32`.
fn new_bigint(val: i32) -> BigInt {
  let (sign, val) = if val >= 0 {
    (Sign::Plus, val as u32)
  } else {
    (Sign::Minus, -val as u32)
  };

  BigInt::from_slice(sign, &[val.to_le()])
}


/// An unlimited precision number type with some improvements and
/// customizations over `BigRational`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Num(BigRational);

impl Num {
  /// Construct a `Num` from two integers.
  pub fn new(numer: i32, denom: u32) -> Self {
    let numer = new_bigint(numer);
    let denom = BigInt::from_slice(Sign::Plus, &[denom.to_le()]);

    Num(BigRational::new(numer, denom))
  }

  /// Construct a `Num` from an integer.
  pub fn from_int(val: i32) -> Self {
    Num(BigRational::from_integer(new_bigint(val)))
  }

  /// Round the given `Num` to the nearest integer.
  ///
  /// Rounding happens based on the Round-Half-To-Even scheme (also
  /// known as the "bankers rounding" algorithm), which rounds to the
  /// closest integer as expected but if the fractional part is exactly
  /// 1/2 (i.e., equidistant from two integers) it rounds to the even
  /// one of the two.
  pub fn round(&self) -> Self {
    Num(round_to_even(&self.0))
  }
}

impl<'de> Deserialize<'de> for Num {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    let s = String::deserialize(deserializer)?;
    let v = Num::from_str(&s)
      .map_err(|_| Error::invalid_value(Unexpected::Str(&s), &"unable to parse string as Num"))?;

    Ok(v)
  }
}

impl Display for Num {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    let hundred = BigRational::from_integer(new_bigint(100));
    let raw = &hundred * &self.0.trunc();
    let value = round_to_even(&(&hundred * &self.0)).trunc();
    let trunc = (&value / hundred).trunc();
    let fract = (&value - &raw).abs();

    write!(fmt, "{}.{}", trunc, fract)
  }
}

impl FromStr for Num {
  type Err = ParseNumError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    fn parse_istr(s: &str) -> Result<BigInt, ParseNumError> {
      Ok(new_bigint(i32::from_str(s)?))
    }

    fn parse_str(s: &str, sign: Sign) -> Result<BigInt, ParseNumError> {
      let num = u32::from_str(s)?;
      let num = BigInt::from_slice(sign, &[num.to_le()]);
      Ok(num)
    }

    let mut splits = s.splitn(2, '.');
    let numer = splits
      .next()
      .ok_or_else(|| ParseNumError::InvalidStrError(s.to_owned()))?;
    let numer = parse_istr(numer)?;

    if let Some(s) = splits.next() {
      let denom = parse_str(s, numer.sign())?;
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

  use serde_json::from_str as from_json;


  #[test]
  fn num_from_int() {
    let num = Num::from_str("42").unwrap();
    assert_eq!(num, Num::from_int(42));
  }

  #[test]
  fn num_from_neg_int() {
    let num = Num::from_str("-37").unwrap();
    assert_eq!(num, Num::from_int(-37));
  }

  #[test]
  fn num_from_min_neg_int() {
    let min = i32::MIN + 1;
    let num = Num::from_str(&min.to_string()).unwrap();
    assert_eq!(num, Num::from_int(-2147483647));
  }

  #[test]
  fn num_from_float() {
    let num = Num::from_str("4000.32").unwrap();
    assert_eq!(num, Num::new(400032, 100));
  }

  #[test]
  fn num_from_neg_float() {
    let num = Num::from_str("-125.398").unwrap();
    assert_eq!(num, Num::new(-125398, 1000));
  }

  #[test]
  fn deserialize_json() {
    let json = r#""37.519""#;
    let num = from_json::<Num>(&json).unwrap();

    assert_eq!(num, Num::new(37519, 1000));
  }

  #[test]
  fn num_int_to_string() {
    let num = Num::from_int(42);
    assert_eq!(num.to_string(), "42.0");
  }

  #[test]
  fn num_neg_int_to_string() {
    let num = Num::from_int(-1337);
    assert_eq!(num.to_string(), "-1337.0");
  }

  #[test]
  fn num_float_to_string() {
    let num = Num::new(49172, 1000);
    assert_eq!(num.to_string(), "49.17");
  }

  #[test]
  fn num_neg_float_to_string() {
    let num = Num::new(-49178, 1000);
    assert_eq!(num.to_string(), "-49.18");
  }

  #[test]
  fn num_round_zero() {
    let num = Num::from_str("0.0").unwrap().round();
    assert_eq!(num, Num::new(0, 1));
  }

  #[test]
  fn num_round_half() {
    let num = Num::from_str("0.5").unwrap().round();
    assert_eq!(num, Num::new(0, 1));
  }

  #[test]
  fn num_round_even() {
    let num = Num::from_str("4000.50").unwrap().round();
    assert_eq!(num, Num::new(4000, 1));
  }

  #[test]
  fn num_round_uneven() {
    let num = Num::from_str("4001.50").unwrap().round();
    assert_eq!(num, Num::new(4002, 1));
  }

  #[test]
  fn num_neg_round_even() {
    let num = Num::from_str("-4000.50").unwrap().round();
    assert_eq!(num, Num::from_int(-4000));
  }

  #[test]
  fn num_neg_round_uneven() {
    let num = Num::from_str("-4001.50").unwrap().round();
    assert_eq!(num, Num::from_int(-4002));
  }
}
