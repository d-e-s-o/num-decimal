// Copyright (C) 2019-2021 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::error::Error as StdError;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
#[cfg(not(feature = "num-v02"))]
use std::num::FpCategory;
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

use num_traits::cast::ToPrimitive;
use num_traits::identities::Zero;
use num_traits::pow::Pow;
use num_traits::sign::Signed;

use crate::num_bigint::BigInt;
use crate::num_bigint::ParseBigIntError;
use crate::num_bigint::Sign;
use crate::num_rational::BigRational;


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

  let zero_ = BigRational::new(zero, one.clone());
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

fn format_impl(
  value: &BigRational,
  mut result: String,
  depth: usize,
  min_precision: usize,
  precision: Option<usize>,
) -> String {
  debug_assert!(min_precision <= precision.unwrap_or(MAX_PRECISION));

  let trunc = value.trunc().to_integer();
  result += &trunc.to_string();

  let numer = value.numer();
  let denom = value.denom();
  let value = numer - (trunc * denom);

  let at_min = depth >= min_precision;
  let at_max = depth >= precision.unwrap_or(MAX_PRECISION);
  // If the user specified a precision for the formatting then we
  // honor that by ensuring that we have that many decimals.
  // Otherwise we print as many as there are, up to `MAX_PRECISION`.
  if (value.is_zero() && precision.is_none() && at_min) || at_max {
    result
  } else {
    if depth == 0 {
      result += ".";
    }

    let value = BigRational::new(value * 10, denom.clone());
    format_impl(&value, result, depth + 1, min_precision, precision)
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


/// An object providing more advanced displaying capabilities to `Num`.
#[derive(Debug)]
pub struct CustomDisplay<'n> {
  /// The `Num` object to display.
  num: &'n Num,
  /// The minimum precision to use when displaying.
  min_precision: Option<usize>,
}

impl<'n> CustomDisplay<'n> {
  /// Create a new `CustomDisplay` object for displaying the given
  /// `Num`.
  fn new(num: &'n Num) -> Self {
    Self {
      num,
      min_precision: None,
    }
  }

  /// Set the minimum precision used when displaying.
  ///
  /// If actual precision is higher, more values will be printed.
  pub fn min_precision(&mut self, min_precision: usize) -> &mut Self {
    self.min_precision = Some(min_precision);
    self
  }
}

impl<'n> Display for CustomDisplay<'n> {
  fn fmt(&self, fmt: &mut Formatter<'_>) -> FmtResult {
    self.num.format(fmt, self.min_precision.unwrap_or(0))
  }
}


/// An unlimited precision number type with some improvements and
/// customizations over `BigRational`.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Num(pub(crate) BigRational);

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

  /// Convert the given `Num` into a `f64`.
  ///
  /// `None` is returned if the numerator or the denominator cannot be
  /// converted into an `f64`.
  pub fn to_f64(&self) -> Option<f64> {
    let numer = self.0.numer().to_f64();
    let denom = self.0.denom().to_f64();

    match (numer, denom) {
      #[cfg(feature = "num-v02")]
      (Some(numer), Some(denom)) => Some(numer / denom),
      #[cfg(not(feature = "num-v02"))]
      (Some(numer), Some(denom)) => {
        if !matches!(numer.classify(), FpCategory::Normal | FpCategory::Zero) {
          return None
        }
        if !matches!(denom.classify(), FpCategory::Normal | FpCategory::Zero) {
          return None
        }
        Some(numer / denom)
      },
      _ => None,
    }
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

  fn format(&self, fmt: &mut Formatter<'_>, min_precision: usize) -> FmtResult {
    let non_negative = !self.0.is_negative();
    let prefix = "";

    let precision = fmt.precision();
    let value = self.round_with(precision.unwrap_or(MAX_PRECISION)).0.abs();
    // We want to print out our value (which is a rational) as a
    // floating point value, for which we need to perform some form of
    // conversion. We do that using what is pretty much text book long
    // division.
    let string = format_impl(&value, String::new(), 0, min_precision, precision);
    fmt.pad_integral(non_negative, prefix, &string)
  }

  /// Retrieve a display adapter that can be used for some more
  /// elaborate formatting needs.
  pub fn display(&self) -> CustomDisplay<'_> {
    CustomDisplay::new(self)
  }
}

impl Default for Num {
  fn default() -> Self {
    Num::from(0)
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
    let min_precision = 0;
    self.format(fmt, min_precision)
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
        return Err(ParseNumError::InvalidStrError(s.to_owned()));
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
