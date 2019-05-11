// Copyright (C) 2019 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::error::Error as StdError;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::i32;
use std::str::FromStr;

use serde::de::Error;
use serde::de::Unexpected;
use serde::de::Visitor;
use serde::Deserialize;
use serde::Deserializer;
use serde::Serialize;
use serde::Serializer;

use num_bigint::BigInt;
use num_bigint::ParseBigIntError;
use num_bigint::Sign;
use num_rational::BigRational;
use num_traits::identities::Zero;
use num_traits::pow::Pow;
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
  ParseIntError(ParseBigIntError),
}

impl From<ParseBigIntError> for ParseNumError {
  fn from(e: ParseBigIntError) -> Self {
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
    struct NumVisitor;

    impl<'de> Visitor<'de> for NumVisitor {
      type Value = Num;

      fn expecting(&self, formatter: &mut Formatter<'_>) -> FmtResult {
        formatter.write_str("a float, an integer, or a string representing either")
      }

      fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
      where
        E: Error,
      {
        Num::from_str(s)
          .map_err(|_| Error::invalid_value(Unexpected::Str(&s), &"a stringified integer/float"))
      }

      fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
      where
        E: Error,
      {
        let s = format!("{}.0", v.to_string());
        Num::from_str(&s)
          .map_err(|_| Error::invalid_value(Unexpected::Str(&s), &"a signed integer"))
      }

      fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
      where
        E: Error,
      {
        let s = format!("{}.0", v.to_string());
        Num::from_str(&s)
          .map_err(|_| Error::invalid_value(Unexpected::Str(&s), &"an unsigned integer"))
      }

      fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
      where
        E: Error,
      {
        // TODO: This is fairly clumsy and introduces an unnecessary
        //       error path. What we really want is a straight
        //       conversion without an intermediate string.
        let s = v.to_string();
        Num::from_str(&s)
          .map_err(|_| Error::invalid_value(Unexpected::Str(&s), &"a floating point value"))
      }
    }

    deserializer.deserialize_any(NumVisitor)
  }
}

impl Serialize for Num {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl Display for Num {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    fn format(value: &BigRational, mut result: String, first: bool) -> String {
      let trunc = value.trunc().to_integer();
      result += &trunc.to_string();

      let numer = value.numer();
      let denom = value.denom();
      let value = numer - (trunc * denom);

      if value.is_zero() {
        result
      } else {
        if first {
          result += ".";
        }

        let value = BigRational::new(value * 10, denom.clone());
        format(&value, result, false)
      }
    }

    // We want to print out our value (which is a rational) as a
    // floating point value, for which we need to perform some form of
    // conversion. We do that using what is pretty much text book long
    // division.
    let sign = if self.0.is_negative() {
      "-"
    } else {
      ""
    };
    write!(fmt, "{}{}", sign, format(&self.0.abs(), String::new(), true))
  }
}

impl FromStr for Num {
  type Err = ParseNumError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    fn parse_istr(s: &str) -> Result<(Sign, BigInt), ParseBigIntError> {
      let val = BigInt::from_str(s)?;

      // BigInt's NoSign is horrible. It represents a value being zero,
      // but it leads to valid data being discarded silently. Work
      // around that.
      let sign = val.sign();
      let sign = if sign == Sign::NoSign {
        if s.starts_with('-') {
          Sign::Minus
        } else {
          Sign::Plus
        }
      } else {
        sign
      };
      Ok((sign, val))
    }

    fn parse_str(s: &str, sign: Sign) -> Result<BigInt, ParseNumError> {
      if s.starts_with('-') || s.starts_with('+') {
        Err(ParseNumError::InvalidStrError(s.to_owned()))?;
      }

      let num = BigInt::parse_bytes(s.as_bytes(), 10)
        .ok_or_else(|| ParseNumError::InvalidStrError(s.to_owned()))?;
      let (_, bytes) = num.to_bytes_le();
      let num = BigInt::from_bytes_le(sign, &bytes);
      Ok(num)
    }

    let mut splits = s.splitn(2, '.');
    let numer = splits
      .next()
      .ok_or_else(|| ParseNumError::InvalidStrError(s.to_owned()))?;
    let (sign, numer) = parse_istr(numer)?;

    if let Some(s) = splits.next() {
      let denom = parse_str(s, sign)?;
      let power = new_bigint(10).pow(s.len());
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
  use serde_json::to_string as to_json;


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
  fn num_from_small_float() {
    let num = Num::from_str("0.20").unwrap();
    assert_eq!(num, Num::new(20, 100));
  }

  #[test]
  fn num_from_long_float() {
    let _ = Num::from_str("207.5873333333333333").unwrap();
  }

  #[test]
  fn num_from_long_neg_float() {
    let _ = Num::from_str("-207.5873333333333333").unwrap();
  }

  #[test]
  fn num_from_small_neg_float() {
    let num = Num::from_str("-0.20").unwrap();
    assert_eq!(num, Num::new(-20, 100));
  }

  #[test]
  fn num_from_neg_float() {
    let num = Num::from_str("-125.398").unwrap();
    assert_eq!(num, Num::new(-125398, 1000));
  }

  #[test]
  fn deserialize_json_string() {
    let json = r#""37.519""#;
    let num = from_json::<Num>(&json).unwrap();

    assert_eq!(num, Num::new(37519, 1000));
  }

  #[test]
  fn deserialize_json_float() {
    let json = r#"126.2633"#;
    let num = from_json::<Num>(&json).unwrap();

    assert_eq!(num, Num::new(1262633, 10000));
  }

  #[test]
  fn deserialize_json_int() {
    let json = r#"356"#;
    let num = from_json::<Num>(&json).unwrap();

    assert_eq!(num, Num::from_int(356));
  }

  #[test]
  fn serialize_json() {
    let num = Num::from_str("14827.9102").unwrap();
    let json = to_json(&num).unwrap();

    assert_eq!(json, r#""14827.9102""#);
  }

  #[test]
  fn zero_to_string() {
    let num = Num::from_int(0);
    assert_eq!(num.to_string(), "0");
  }

  #[test]
  fn one_to_string() {
    let num = Num::from_int(1);
    assert_eq!(num.to_string(), "1");
  }

  #[test]
  fn num_int_to_string() {
    let num = Num::from_int(42);
    assert_eq!(num.to_string(), "42");
  }

  #[test]
  fn num_neg_int_to_string() {
    let num = Num::from_int(-1337);
    assert_eq!(num.to_string(), "-1337");
  }

  #[test]
  fn num_float_to_string() {
    let num = Num::new(49172, 1000);
    assert_eq!(num.to_string(), "49.172");
  }

  #[test]
  fn num_neg_float_to_string() {
    let num = Num::new(-49178, 1000);
    assert_eq!(num.to_string(), "-49.178");
  }

  #[test]
  fn num_from_string_and_back() {
    let num = Num::from_str("96886.19").unwrap();
    assert_eq!(num.to_string(), "96886.19");
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

  #[test]
  fn num_from_invalid_str() {
    let _ = Num::from_str("1992.+50").unwrap_err();
    let _ = Num::from_str("37.-4").unwrap_err();
    let _ = Num::from_str("-44.-15").unwrap_err();
  }
}
