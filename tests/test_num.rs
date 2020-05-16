// Copyright (C) 2020 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::unreadable_literal)]

use std::i32;
use std::ops::Neg;
use std::str::FromStr;

use num_bigint::BigInt;
use num_traits::NumAssignOps;
use num_traits::NumOps;

use num_decimal::Num;
use num_decimal::ParseNumError;


#[test]
fn default_num() {
  let num = Num::default();
  assert_eq!(num, Num::from(0));
}

#[test]
fn num_from_int() {
  let num = Num::from_str("42").unwrap();
  assert_eq!(num, Num::from(42));
}

#[test]
fn num_from_neg_int() {
  let num = Num::from_str("-37").unwrap();
  assert_eq!(num, Num::from(-37));
}

#[test]
fn num_from_min_neg_int() {
  let min = i32::MIN + 1;
  let num = Num::from_str(&min.to_string()).unwrap();
  assert_eq!(num, Num::from(-2147483647));
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
  assert_eq!(num.to_string(), "0.33333333")
}

#[test]
fn num_max_precision_with_rounding() {
  let num = Num::new(2, 3);
  assert_eq!(num.to_string(), "0.66666667")
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
  assert_eq!(format!("{}", Num::new(1, 2).display().min_precision(2)), "0.50");
  assert_eq!(format!("{}", Num::new(1, 3).display().min_precision(2)), "0.33333333");
  assert_eq!(format!("{}", Num::new(2, 3).display().min_precision(2)), "0.66666667");
  assert_eq!(format!("{}", Num::new(1, 3).display()), "0.33333333");
  assert_eq!(format!("{}", Num::new(2, 3).display()), "0.66666667");
  assert_eq!(format!("{:.2}", Num::new(1, 3).display()), "0.33");
  assert_eq!(format!("{:.2}", Num::new(2, 3).display()), "0.67");
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
fn num_from_invalid_str() {
  let err = Num::from_str("abc.+50").unwrap_err();
  assert!(matches!(err, ParseNumError::ParseIntError(..)), err);

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
  assert_eq!(
    Num::from(u128::max_value()).to_string(),
    u128::max_value().to_string()
  );
  assert_eq!(
    Num::from(i128::min_value()).to_string(),
    i128::min_value().to_string()
  );
  assert_eq!(&Num::from(BigInt::from(1)).to_string(), "1");
}
