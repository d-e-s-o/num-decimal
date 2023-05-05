// Copyright (C) 2020-2022 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_unit_value, clippy::unreadable_literal)]

use std::convert::TryFrom as _;
use std::convert::TryInto as _;
use std::i32;
use std::ops::Neg;
use std::str::FromStr;

use num_traits::NumAssignOps;
use num_traits::NumOps;

use num_decimal::num_bigint::BigInt;
use num_decimal::Num;
use num_decimal::Num32;
use num_decimal::Num64;
use num_decimal::ParseNumError;


/// Check that we can default create a [`Num`].
#[test]
fn default_num() {
  let num = Num::default();
  assert_eq!(num, Num::from(0));
}

/// Check that we can default create a [`Num32`].
#[test]
fn default_num32() {
  let num = Num32::default();
  assert_eq!(num, Num32::from(0));
}

/// Check that we can default create a [`Num64`].
#[test]
fn default_num64() {
  let num = Num64::default();
  assert_eq!(num, Num64::from(0));
}

/// Check that we can create a new [`Num`] object from an integer.
#[test]
fn num_from_int() {
  let num = Num::from(-1234567);
  assert_eq!(num, Num::new(-1234567, 1));
}

/// Check that we can create a new [`Num32`] object from an integer.
#[test]
fn num32_from_int() {
  let num = Num::from(98765);
  assert_eq!(num, Num::new(98765, 1));
}

/// Check that we can create a new [`Num64`] object from an integer.
#[test]
fn num64_from_int() {
  let num = Num::from(-1);
  assert_eq!(num, Num::new(-1, 1));
}

/// Check that we can convert a [`Num`] into a [`Num32`], assuming that
/// it can be represented.
#[test]
fn num32_from_num() {
  let num = Num::new(1234567, 31289);
  let num32 = Num32::try_from(num).unwrap();
  assert_eq!(num32, Num32::new(1234567, 31289));
}

/// Check that conversion of a [`Num`] into a [`Num32`] fails if it
/// cannot be represented correctly.
#[test]
fn num32_from_num_failure() {
  let num = Num::new(u64::MAX, 1);
  let () = Num32::try_from(&num).unwrap_err();
}

/// Check that we can convert a [`Num`] into a [`Num64`], assuming that
/// it can be represented.
#[test]
fn num64_from_num() {
  let num = Num::new(1234567, 31289);
  let num64 = Num64::try_from(&num).unwrap();
  assert_eq!(num64, Num64::new(1234567, 31289));
}

/// Check that conversion of a [`Num`] into a [`Num64`] fails if it
/// cannot be represented correctly.
#[test]
fn num64_from_num_failure() {
  let num = Num::new(u128::MAX, 1);
  let () = Num64::try_from(num).unwrap_err();
}

/// Check that we can approximate a [`Num`] with a [`Num32`] when the
/// number can't really be represented.
#[test]
fn num32_approximate_out_of_bounds_num() {
  let num = Num::new(i128::MAX, 1);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MAX, 1));

  let num = Num::new(i128::MIN, 1);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MIN, 1));

  let num = Num::new(i128::MAX, 1u128 << 96);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MAX, 1));

  let num = Num::new(i128::MIN, 1i128 << 96);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MIN, 1));

  let num = Num::new(i128::MAX, i64::MAX);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MAX, 1));

  let num = Num::new(i128::MAX, i64::MIN);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MIN, 1));

  let num = Num::new(1u128 << 64, 1u64 << 33);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MAX, 1));

  let num = Num::new(1u128 << 64, -(1i64 << 33));
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(i32::MIN, 1));
}

/// Check that we can approximate a [`Num`] with a [`Num32`], when the
/// number can be represented without approximation.
#[test]
fn num32_approximate_representable_num() {
  let num = Num::new(1u128 << 64, 1u64 << 34);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(1i32 << 30, 1));

  let num = Num::new(-(1i128 << 64), 1u64 << 34);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(1i32 << 30, -1));

  let num = Num::new(127659574, 1000000000);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(63829787, 500000000));

  let num = Num::new(-127659574, 1000000000);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(-63829787, 500000000));

  let num = Num::new(415, 93);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(415, 93));

  let num = Num::new(20, 3);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(20, 3));

  let num = Num::new(-20, 3);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(-20, 3));
}

/// Check that we can approximate a [`Num`] with a [`Num32`].
#[test]
fn num32_approximate_num() {
  let num = Num::new(i128::MAX, i128::MAX - 1);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(1, 1));

  let num = Num::new(i128::MIN, i128::MAX - 1);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(-1, 1));

  let num = Num::new(i128::MIN, i128::MIN + 1);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(1, 1));

  let num = Num::new(3 * (i32::MAX as i64), 13);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(1486719448, 3));

  let num = Num::new(-3 * (i32::MAX as i64), 13);
  let num32 = Num32::approximate(num);
  assert_eq!(num32, Num32::new(-1486719448, 3));
}

/// Test that we can convert a [`Num32`] object into a [`Num`].
#[test]
fn num_from_num32() {
  let num32 = Num32::new(10, 3);
  let num = Num::from(num32);
  assert_eq!(num, Num::new(10, 3))
}

/// Test that we can convert a [`Num64`] object into a [`Num`].
#[test]
fn num_from_num64() {
  let num64 = Num64::new(1, 3);
  let num = Num::from(num64);
  assert_eq!(num, Num::new(1, 3))
}

/// Check that we can convert a [`Num`] into its constituent numerator
/// and denominator.
#[test]
fn num_into() {
  let num = Num::new(1234567, 98765);
  assert_eq!(
    <(BigInt, BigInt)>::from(num),
    (BigInt::from(1234567), BigInt::from(98765))
  );
}

/// Check that we can convert a [`Num32`] into its constituent numerator
/// and denominator.
#[test]
fn num32_into() {
  let num32 = Num32::new(1234567, 98765);
  assert_eq!(<(i32, i32)>::from(num32), (1234567, 98765));
}

/// Check that we can convert a [`Num64`] into its constituent numerator
/// and denominator.
#[test]
fn num64_into() {
  let num64 = Num64::new(1234567, 98765);
  assert_eq!(<(i64, i64)>::from(num64), (1234567, 98765));
}

#[test]
fn num_from_int_str() {
  let num = Num::from_str("42").unwrap();
  assert_eq!(num, Num::from(42));
}

#[test]
fn num_from_neg_int_str() {
  let num = Num::from_str("-37").unwrap();
  assert_eq!(num, Num::from(-37));
}

#[test]
fn num_from_min_neg_int_str() {
  let min = i32::MIN + 1;
  let num = Num::from_str(&min.to_string()).unwrap();
  assert_eq!(num, Num::from(-2147483647));
}

#[test]
fn num_from_float_str() {
  let num = Num::from_str("4000.32").unwrap();
  assert_eq!(num, Num::new(400032, 100));
}

#[test]
fn num_from_small_float_str() {
  let num = Num::from_str("0.20").unwrap();
  assert_eq!(num, Num::new(20, 100));
}

#[test]
fn num_from_long_float_str() {
  let _ = Num::from_str("207.5873333333333333").unwrap();
}

#[test]
fn num_from_long_neg_float_str() {
  let _ = Num::from_str("-207.5873333333333333").unwrap();
}

#[test]
fn num_from_small_neg_float_str() {
  let num = Num::from_str("-0.20").unwrap();
  assert_eq!(num, Num::new(-20, 100));
}

#[test]
fn num_from_neg_float_str() {
  let num = Num::from_str("-125.398").unwrap();
  assert_eq!(num, Num::new(-125398, 1000));
}

#[test]
fn zero_to_string() {
  let num = Num::from(0);
  assert_eq!(num.to_string(), "0");
}

#[test]
fn one_to_string() {
  let num = Num::from(1);
  assert_eq!(num.to_string(), "1");
}

#[test]
fn num_int_to_string() {
  let num = Num::from(42);
  assert_eq!(num.to_string(), "42");
}

#[test]
fn num_neg_int_to_string() {
  let num = Num::from(-1337);
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
fn num_format_padded() {
  let num = Num::new(-257, 100);
  assert_eq!(format!("{:>8}", num), "   -2.57");
}

#[test]
fn num_format_precision() {
  let num = Num::new(261, 100);
  assert_eq!(format!("{:.1}", num), "2.6");
}

#[test]
fn num_format_precision_round() {
  let num = Num::new(-259, 1000);
  assert_eq!(format!("{:.2}", num), "-0.26");
}

#[test]
fn num_max_precision() {
  let num = Num::new(1, 3);
  assert_eq!(num.to_string(), "0.333333333")
}

#[test]
fn num_max_precision_with_rounding() {
  let num = Num::new(2, 3);
  assert_eq!(num.to_string(), "0.666666667")
}

#[test]
fn num_max_custom_precision() {
  let num = Num::new(1, 3);
  assert_eq!(format!("{:.32}", num), "0.33333333333333333333333333333333")
}

#[test]
fn num_max_custom_precision_with_rounding() {
  let num = Num::new(2, 3);
  assert_eq!(format!("{:.32}", num), "0.66666666666666666666666666666667")
}

#[test]
fn num_precision_round_to_zero() {
  let actual = format!("{:.2}", Num::from_str("-0.001").unwrap());
  let expected = format!("{:.2}", -0.001f64);
  assert_eq!(actual, expected)
}

#[test]
fn num_precision_fill_zeros() {
  let actual = format!("{:.3}", Num::from(5));
  let expected = format!("{:.3}", 5.0f64);
  assert_eq!(actual, expected)
}

#[test]
fn num_minimum_precision() {
  assert_eq!(
    format!("{}", Num::new(1, 2).display().min_precision(2)),
    "0.50"
  );
  assert_eq!(
    format!("{}", Num::new(1, 3).display().min_precision(2)),
    "0.333333333"
  );
  assert_eq!(
    format!("{}", Num::new(2, 3).display().min_precision(2)),
    "0.666666667"
  );
  assert_eq!(format!("{}", Num::new(1, 3).display()), "0.333333333");
  assert_eq!(format!("{}", Num::new(2, 3).display()), "0.666666667");
  assert_eq!(format!("{:.2}", Num::new(1, 3).display()), "0.33");
  assert_eq!(format!("{:.2}", Num::new(2, 3).display()), "0.67");
}

/// Check that our [`Num`] debug representation is as expected.
#[test]
fn num_debug_format() {
  assert_eq!(format!("{:?}", Num::new(1, 2)), "1/2");
  assert_eq!(format!("{:?}", Num::new(1, -3)), "-1/3");
  assert_eq!(format!("{:?}", Num::new(-3, 8)), "-3/8");
}

/// Check that our [`Num32`] debug representation is as expected.
#[test]
fn num32_debug_format() {
  assert_eq!(format!("{:?}", Num32::new(1, 2)), "1/2");
  assert_eq!(format!("{:?}", Num32::new(1, -3)), "-1/3");
  assert_eq!(format!("{:?}", Num32::new(-3, 8)), "-3/8");
}

/// Check that our [`Num64`] debug representation is as expected.
#[test]
fn num64_debug_format() {
  assert_eq!(format!("{:?}", Num64::new(1, 2)), "1/2");
  assert_eq!(format!("{:?}", Num64::new(1, -3)), "-1/3");
  assert_eq!(format!("{:?}", Num64::new(-3, 8)), "-3/8");
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
  assert_eq!(num, Num::from(-4000));
}

#[test]
fn num_neg_round_uneven() {
  let num = Num::from_str("-4001.50").unwrap().round();
  assert_eq!(num, Num::from(-4002));
}

#[test]
fn num_trunc() {
  let num = Num::from_str("1.1").unwrap().trunc();
  assert_eq!(num, Num::from(1));
}

#[test]
fn num_fract() {
  let num = Num::from_str("1.1").unwrap().fract();
  assert_eq!(num, Num::from_str("0.1").unwrap());
}

#[test]
fn num_to_integer() {
  let num = Num::from_str("42.1").unwrap().to_integer();
  assert_eq!(num, BigInt::from(42));
}

#[test]
fn num_to_i64() {
  let val = Num::from_str("-1337.8").unwrap().to_i64().unwrap();
  assert_eq!(val, -1337);
}

#[test]
fn num_to_i64_underflow() {
  let val = Num::from_str("-9223372036854775809").unwrap().to_u64();
  assert_eq!(val, None);
}

#[test]
fn num_to_u64() {
  let val = Num::from_str("31267.916721").unwrap().to_u64().unwrap();
  assert_eq!(val, 31267);
}

#[test]
fn num_to_u64_overflow() {
  let val = Num::from_str("18446744073709551616").unwrap().to_u64();
  assert_eq!(val, None);
}

#[test]
fn num_to_f64() {
  let val = Num::from_str("1.25").unwrap().to_f64().unwrap();
  // We convert the float value into a string for comparison matters.
  assert_eq!(val.to_string(), "1.25");

  let val = Num::from_str("-1.25").unwrap().to_f64().unwrap();
  assert_eq!(val.to_string(), "-1.25");
}

#[test]
fn num_to_f64_failure() {
  let count = f64::MAX_10_EXP.try_into().unwrap();
  // Create a number large enough to not fit into an f64.
  let num = (0..=count).fold(String::with_capacity(count), |mut num, _| {
    num.push('9');
    num
  });
  let val = Num::from_str(&num).unwrap().to_f64();
  assert_eq!(val, None);
}

#[test]
fn num_from_invalid_str() {
  let err = Num::from_str("abc.+50").unwrap_err();
  assert!(matches!(err, ParseNumError::ParseIntError(..)), "{}", err);

  let err = Num::from_str("1992.+50").unwrap_err();
  assert_eq!(err, ParseNumError::InvalidStrError("+50".to_string()));

  let _ = Num::from_str("37.-4").unwrap_err();
  let _ = Num::from_str("-44.-15").unwrap_err();
}

fn implements_various_num_traits<T>(_num: T)
where
  // Note that we currently do not implement `NumAssign` which is a
  // requirement for `NumAssignRef`. So we can't require that
  // directly.
  T: NumOps + for<'r> NumOps<&'r T> + NumAssignOps + for<'r> NumAssignOps<&'r T>,
{
}

#[test]
fn num_assign_ops() {
  let num = Num::from(1);
  implements_various_num_traits(num)
}

#[test]
fn num_neg() {
  assert_eq!(Num::from(2).neg(), Num::from(-2));
  assert_eq!(-Num::from(3), Num::from(-3));
  assert_eq!(-&Num::from(4), Num::from(-4));
}

#[test]
fn num_add() {
  let lhs = Num::from(2);
  let rhs = Num::from(3);
  assert_eq!(lhs + rhs, Num::from(5));
}

#[test]
fn num_add_integer() {
  let lhs = Num::from(2);
  assert_eq!(lhs + 3, Num::from(5));
}

#[test]
fn num_sub() {
  let lhs = Num::from(3);
  let rhs = Num::from(2);
  assert_eq!(lhs - rhs, Num::from(1));
}

#[test]
fn num_sub_integer() {
  let lhs = Num::from(3);
  assert_eq!(lhs - 2, Num::from(1));
}

#[test]
fn num_mul() {
  let lhs = Num::from(2);
  let rhs = Num::from(3);
  assert_eq!(lhs * rhs, Num::from(6));
}

#[test]
fn num_mul_integer() {
  let lhs = Num::from(2);
  assert_eq!(lhs * 3, Num::from(6));
}

#[test]
fn num_div() {
  let lhs = Num::from(8);
  let rhs = Num::from(2);
  assert_eq!(lhs / rhs, Num::from(4));
}

#[test]
fn num_div_integer() {
  let lhs = Num::from(8);
  assert_eq!(lhs / 2, Num::from(4));
}

#[test]
fn num_rem() {
  let lhs = Num::from(3);
  let rhs = Num::from(2);
  assert_eq!(lhs % rhs, Num::from(1));
}

#[test]
fn num_rem_integer() {
  let lhs = Num::from(3);
  assert_eq!(lhs % 2, Num::from(1));
}

#[test]
fn num_add_assign() {
  let mut lhs = Num::from(2);
  let rhs = Num::from(3);
  lhs += rhs;
  assert_eq!(lhs, Num::from(5));
}

#[test]
fn num_add_assign_integer() {
  let mut lhs = Num::from(2);
  lhs += 3;
  assert_eq!(lhs, Num::from(5));
}

#[test]
fn num_sub_assign() {
  let mut lhs = Num::from(3);
  let rhs = Num::from(2);
  lhs -= rhs;
  assert_eq!(lhs, Num::from(1));
}

#[test]
fn num_sub_assign_integer() {
  let mut lhs = Num::from(3);
  lhs -= 2;
  assert_eq!(lhs, Num::from(1));
}

#[test]
fn num_mul_assign() {
  let mut lhs = Num::from(2);
  let rhs = Num::from(3);
  lhs *= rhs;
  assert_eq!(lhs, Num::from(6));
}

#[test]
fn num_mul_assign_integer() {
  let mut lhs = Num::from(2);
  lhs *= 3;
  assert_eq!(lhs, Num::from(6));
}

#[test]
fn num_div_assign() {
  let mut lhs = Num::from(8);
  let rhs = Num::from(2);
  lhs /= rhs;
  assert_eq!(lhs, Num::from(4));
}

#[test]
fn num_div_assign_integer() {
  let mut lhs = Num::from(8);
  lhs /= 2;
  assert_eq!(lhs, Num::from(4));
}

#[test]
fn num_rem_assign() {
  let mut lhs = Num::from(3);
  let rhs = Num::from(2);
  lhs %= rhs;
  assert_eq!(lhs, Num::from(1));
}

#[test]
fn num_rem_assign_integer() {
  let mut lhs = Num::from(3);
  lhs %= 2;
  assert_eq!(lhs, Num::from(1));
}

#[test]
fn check_zero() {
  assert!(Num::from(0).is_zero());
  assert!(Num::new(0, 12).is_zero());
  assert!((Num::new(26, 2) - Num::from(13)).is_zero());
}

#[test]
fn check_positive() {
  assert!(!Num::from(0).is_positive());
  assert!(Num::from(2).is_positive());
  assert!(!(Num::new(26, 2) - Num::from(14)).is_positive());
}

#[test]
fn check_negative() {
  assert!(!Num::from(0).is_negative());
  assert!(Num::from(-1).is_negative());
  assert!(!(Num::new(26, 2) - Num::from(12)).is_negative());
}

#[test]
fn debug_format() {
  assert_eq!(format!("{:?}", Num::new(-1337, 42)), "-191/6");
}

#[test]
fn from() {
  assert_eq!(&Num::from(42usize).to_string(), "42");
  assert_eq!(&Num::from(255u8).to_string(), "255");
  assert_eq!(Num::from(u128::MAX).to_string(), u128::MAX.to_string());
  assert_eq!(Num::from(i128::MIN).to_string(), i128::MIN.to_string());
  assert_eq!(&Num::from(BigInt::from(1)).to_string(), "1");
}
