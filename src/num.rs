// Copyright (C) 2019-2020 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::error::Error as StdError;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::str::FromStr;

#[cfg(feature = "serde")]
use serde::{
  de::{
    Error,
    Unexpected,
    Visitor,
  },
  Deserialize,
  Deserializer,
  Serialize,
  Serializer,
};

use num_bigint::BigInt;
use num_bigint::ParseBigIntError;
use num_bigint::Sign;
use num_rational::BigRational;
use num_traits::cast::ToPrimitive;
use num_traits::identities::Zero;
use num_traits::pow::Pow;
use num_traits::sign::Signed;


/// The maximum precision we use when converting a `Num` into a string.
///
/// Because we base our implementation on rational numbers which can map
/// to an infinite sequence in the decimal system we have to put an
/// upper limit on the maximum precision we can display.
const MAX_PRECISION: usize = 8;


/// Round the given `BigRational` to the nearest integer. Rounding
/// happens based on the Round-Half-To-Even scheme (also known as the
/// "banker's rounding" algorithm), which rounds to the closest integer
/// as expected but if the fractional part is exactly 1/2 (i.e.,
/// equidistant from two integers) it rounds to the even one of the two.
fn round_to_even(val: &BigRational) -> BigRational {
  let zero = BigInt::from(0);
  let one = BigInt::from(1);
  let two = BigInt::from(2);

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
#[derive(Debug, PartialEq)]
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

impl StdError for ParseNumError {
  fn source(&self) -> Option<&(dyn StdError + 'static)> {
    match self {
      Self::InvalidStrError(..) => None,
      Self::ParseIntError(err) => err.source(),
    }
  }
}


/// An unlimited precision number type with some improvements and
/// customizations over `BigRational`.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Num(BigRational);

impl Num {
  /// Construct a `Num` from two integers.
  pub fn new<T, U>(numer: T, denom: U) -> Self
  where
    BigInt: From<T>,
    BigInt: From<U>,
  {
    let numer = BigInt::from(numer);
    let denom = BigInt::from(denom);

    Num(BigRational::new(numer, denom))
  }

  /// Round the given `Num` to the nearest integer.
  ///
  /// Rounding happens based on the Round-Half-To-Even scheme (also
  /// known as the "bankers rounding" algorithm), which rounds to the
  /// closest integer as expected but if the fractional part is exactly
  /// 1/2 (i.e., equidistant from two integers) it rounds to the even
  /// one of the two.
  pub fn round(&self) -> Self {
    self.round_with(0)
  }

  /// Round the given `Num` with the given precision.
  ///
  /// Rounding happens based on the Round-Half-To-Even scheme similar to
  /// `round`.
  pub fn round_with(&self, precision: usize) -> Self {
    let factor = BigInt::from(10).pow(precision);
    let value = &self.0 * &factor;

    Num(round_to_even(&value).trunc() / factor)
  }

  /// Round the given `Num` towards zero.
  pub fn trunc(&self) -> Self {
    Num(self.0.trunc())
  }

  /// Return the fractional part of the given `Num`, with division rounded towards zero.
  pub fn fract(&self) -> Self {
    Num(self.0.fract())
  }

  /// Convert the given `Num` to an integer, rounding towards zero.
  pub fn to_integer(&self) -> BigInt {
    self.0.to_integer()
  }

  /// Convert the given `Num` into a `u64`.
  ///
  /// The value will be converted into an integer, with rounding towards
  /// zero. `None` is returned if the resulting integer does not fit
  /// into 64 bit.
  pub fn to_i64(&self) -> Option<i64> {
    self.to_integer().to_i64()
  }

  /// Convert the given `Num` into a `u64`.
  ///
  /// The value will be converted into an integer, with rounding towards
  /// zero. `None` is returned if the resulting integer does not fit
  /// into 64 bit.
  pub fn to_u64(&self) -> Option<u64> {
    self.to_integer().to_u64()
  }

  /// Check if the given `Num` is zero.
  pub fn is_zero(&self) -> bool {
    self.0.is_zero()
  }

  /// Check if the given `Num` is positive.
  pub fn is_positive(&self) -> bool {
    self.0.is_positive()
  }

  /// Check if the given `Num` is negative.
  pub fn is_negative(&self) -> bool {
    self.0.is_negative()
  }
}

impl Default for Num {
  fn default() -> Self {
    Num::from(0)
  }
}

#[cfg(feature = "serde")]
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

#[cfg(feature = "serde")]
impl Serialize for Num {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

// The default `Debug` implementation is way too verbose. We have no
// intention of debugging `BigRational` itself. So we overwrite it here,
// effectively printing a fraction.
impl Debug for Num {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    // We maintain the invariant that the numerator determines the sign
    // and that the denominator is always positive (as it can never be
    // zero).
    debug_assert!(self.0.denom().is_positive());

    write!(fmt, "{}/{}", self.0.numer(), self.0.denom())
  }
}

impl Display for Num {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    fn format(
      value: &BigRational,
      mut result: String,
      depth: usize,
      precision: Option<usize>,
    ) -> String {
      let trunc = value.trunc().to_integer();
      result += &trunc.to_string();

      let numer = value.numer();
      let denom = value.denom();
      let value = numer - (trunc * denom);

      // If the user specified a precision for the formatting then we
      // honor that by ensuring that we have that many decimals.
      // Otherwise we print as many as there are, up to `MAX_PRECISION`.
      if (value.is_zero() && precision.is_none()) || depth >= precision.unwrap_or(MAX_PRECISION) {
        result
      } else {
        if depth == 0 {
          result += ".";
        }

        let value = BigRational::new(value * 10, denom.clone());
        format(&value, result, depth + 1, precision)
      }
    }

    let non_negative = !self.0.is_negative();
    let prefix = "";

    let precision = fmt.precision();
    let value = self.round_with(precision.unwrap_or(MAX_PRECISION)).0.abs();
    // We want to print out our value (which is a rational) as a
    // floating point value, for which we need to perform some form of
    // conversion. We do that using what is pretty much text book long
    // division.
    let string = format(&value, String::new(), 0, precision);
    fmt.pad_integral(non_negative, prefix, &string)
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
      let power = BigInt::from(10).pow(s.len());
      let numer = numer * &power + denom;
      Ok(Num(BigRational::new(numer, power)))
    } else {
      Ok(Num(BigRational::from_integer(numer)))
    }
  }
}


macro_rules! impl_from {
  ($type:ty) => {
    impl From<$type> for Num {
      #[inline]
      fn from(val: $type) -> Self {
        Self(BigRational::from_integer(BigInt::from(val)))
      }
    }
  };
}

impl_from!(i128);
impl_from!(i16);
impl_from!(i32);
impl_from!(i64);
impl_from!(i8);
impl_from!(isize);
impl_from!(u128);
impl_from!(u16);
impl_from!(u32);
impl_from!(u64);
impl_from!(u8);
impl_from!(usize);
impl_from!(BigInt);


macro_rules! impl_neg {
  ($lhs:ty) => {
    impl Neg for $lhs {
      type Output = Num;

      #[inline]
      fn neg(self) -> Self::Output {
        let Num(int) = self;
        Num(int.neg())
      }
    }
  };
}

impl_neg!(Num);
impl_neg!(&Num);


macro_rules! impl_op {
  (impl $imp:ident, $method:ident, $lhs:ty, $rhs:ty) => {
    impl $imp<$rhs> for $lhs {
      type Output = Num;

      #[inline]
      fn $method(self, rhs: $rhs) -> Self::Output {
        let Num(lhs) = self;
        let Num(rhs) = rhs;
        Num(lhs.$method(rhs))
      }
    }
  };
}

macro_rules! impl_int_op {
  (impl $imp:ident, $method:ident, $lhs:ty) => {
    // Unfortunately we are only able to allow for right hand side
    // integer types in the operation.
    impl<T> $imp<T> for $lhs
    where
      BigInt: From<T>,
    {
      type Output = Num;

      #[inline]
      fn $method(self, rhs: T) -> Self::Output {
        let Num(lhs) = self;
        let rhs = BigRational::from_integer(BigInt::from(rhs));
        Num(lhs.$method(rhs))
      }
    }
  };
}

macro_rules! impl_ops {
  (impl $imp:ident, $method:ident) => {
    impl_op!(impl $imp, $method, Num, Num);
    impl_op!(impl $imp, $method, &Num, Num);
    impl_op!(impl $imp, $method, Num, &Num);
    impl_op!(impl $imp, $method, &Num, &Num);
    impl_int_op!(impl $imp, $method, Num);
    impl_int_op!(impl $imp, $method, &Num);
  };
}

impl_ops!(impl Add, add);
impl_ops!(impl Sub, sub);
impl_ops!(impl Mul, mul);
impl_ops!(impl Div, div);
impl_ops!(impl Rem, rem);


macro_rules! impl_assign_op {
  (impl $imp:ident, $method:ident, $lhs:ty, $rhs:ty) => {
    impl $imp<$rhs> for $lhs {
      #[inline]
      fn $method(&mut self, rhs: $rhs) {
        let Num(rhs) = rhs;
        (self.0).$method(rhs)
      }
    }
  };
}

macro_rules! impl_assign_ops {
  (impl $imp:ident, $method:ident) => {
    impl<T> $imp<T> for Num
    where
      BigInt: From<T>,
    {
      #[inline]
      fn $method(&mut self, rhs: T) {
        let rhs = BigRational::from_integer(BigInt::from(rhs));
        (self.0).$method(rhs)
      }
    }

    impl_assign_op!(impl $imp, $method, Num, Num);
    impl_assign_op!(impl $imp, $method, Num, &Num);
  };
}

impl_assign_ops!(impl AddAssign, add_assign);
impl_assign_ops!(impl SubAssign, sub_assign);
impl_assign_ops!(impl MulAssign, mul_assign);
impl_assign_ops!(impl DivAssign, div_assign);
impl_assign_ops!(impl RemAssign, rem_assign);


#[cfg(test)]
#[cfg(feature = "serde")]
mod tests {
  use super::*;


  use serde_json::{
    from_str as from_json,
    to_string as to_json,
  };


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

    assert_eq!(num, Num::from(356));
  }

  #[test]
  fn serialize_json() {
    let num = Num::from_str("14827.9102").unwrap();
    let json = to_json(&num).unwrap();

    assert_eq!(json, r#""14827.9102""#);
  }
}
