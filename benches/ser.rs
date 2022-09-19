// Copyright (C) 2022 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![feature(test)]

extern crate test;

use std::str::FromStr;

use bincode::deserialize as from_bincode;
use bincode::serialize as to_bincode;

use num_decimal::Num;

use serde_json::from_str as from_json;
use serde_json::to_string as to_json;

use test::Bencher;

/// Benchmark round trip JSON conversions of zero.
#[bench]
fn json_roundtrip_zero(b: &mut Bencher) {
  let num = Num::from_str("0").unwrap();
  b.iter(|| from_json::<Num>(&to_json(&num).unwrap()).unwrap())
}

/// Benchmark round trip JSON conversions of a "large" number.
#[bench]
fn json_roundtrip_large(b: &mut Bencher) {
  let num = Num::from_str("14827.9102").unwrap();
  b.iter(|| from_json::<Num>(&to_json(&num).unwrap()).unwrap())
}

/// Benchmark round trip bincode conversions of zero.
#[bench]
fn bincode_roundtrip_zero(b: &mut Bencher) {
  let num = Num::from_str("0").unwrap();
  b.iter(|| from_bincode::<Num>(&to_bincode(&num).unwrap()).unwrap())
}

/// Benchmark round trip bincode conversions of a "large" number.
#[bench]
fn bincode_roundtrip_large(b: &mut Bencher) {
  let num = Num::from_str("14827.9102").unwrap();
  b.iter(|| from_bincode::<Num>(&to_bincode(&num).unwrap()).unwrap())
}
