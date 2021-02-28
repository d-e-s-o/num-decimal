// Copyright (C) 2021 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::str::FromStr as _;

use num_bigint::BigInt;
use num_bigint::Sign;
use num_rational::BigRational;

use serde::de::Error;
use serde::de::Unexpected;
use serde::de::Visitor;
use serde::Deserialize;
use serde::Deserializer;
use serde::Serialize;
use serde::Serializer;

use crate::Num;


/// A sign type that can be serialized and deserialized.
#[derive(Debug, Deserialize, Serialize)]
#[repr(u8)]
enum SerdeSign {
  Minus,
  NoSign,
  Plus,
}

impl From<Sign> for SerdeSign {
  fn from(other: Sign) -> Self {
    match other {
      Sign::Minus => Self::Minus,
      Sign::NoSign => Self::NoSign,
      Sign::Plus => Self::Plus,
    }
  }
}

impl Into<Sign> for SerdeSign {
  fn into(self) -> Sign {
    match self {
      Self::Minus => Sign::Minus,
      Self::NoSign => Sign::NoSign,
      Self::Plus => Sign::Plus,
    }
  }
}


/// A tuple representing a ratio that can easily be serialized and
/// deserialized.
#[derive(Debug, Deserialize, Serialize)]
struct SerdeRatio(SerdeSign, Vec<u8>, Vec<u8>);

use std::ops::Mul as _;
impl From<&Num> for SerdeRatio {
  fn from(other: &Num) -> Self {
    // We could get away without the dedicated `SerdeSign` type by using
    // `BigInt::to_signed_bytes_le`, but that seems to be much more
    // expensive, computationally.
    let (nsign, nbytes) = other.0.numer().to_bytes_le();
    let (dsign, dbytes) = other.0.denom().to_bytes_le();

    Self(nsign.mul(dsign).into(), nbytes, dbytes)
  }
}

impl Into<Num> for SerdeRatio {
  fn into(self) -> Num {
    let SerdeRatio(sign, nbytes, dbytes) = self;

    let numer = BigInt::from_bytes_le(sign.into(), &nbytes);
    let denom = BigInt::from_bytes_le(Sign::Plus, &dbytes);

    Num(BigRational::new_raw(numer, denom))
  }
}


impl<'de> Deserialize<'de> for Num {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct HumanReadable;

    impl<'de> Visitor<'de> for HumanReadable {
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

    if deserializer.is_human_readable() {
      deserializer.deserialize_any(HumanReadable)
    } else {
      SerdeRatio::deserialize(deserializer).map(SerdeRatio::into)
    }
  }
}


impl Serialize for Num {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    if serializer.is_human_readable() {
      serializer.serialize_str(&self.to_string())
    } else {
      let ratio = SerdeRatio::from(self);
      SerdeRatio::serialize(&ratio, serializer)
    }
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use bincode::deserialize as from_bincode;
  use bincode::serialize as to_bincode;

  use serde_json::from_str as from_json;
  use serde_json::to_string as to_json;


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

  /// Check that we can serialize to `bincode` and back.
  #[test]
  fn serialize_deserialize_bincode() {
    let num = Num::from_str("13377.4290217").unwrap();
    let new = from_bincode(&to_bincode(&num).unwrap()).unwrap();

    assert_eq!(num, new);
  }

  /// Check that we can serialize a negative `Num` to `bincode` and
  /// back.
  #[test]
  fn serialize_deserialize_bincode_negative() {
    let num = Num::from_str("-13377.4290217").unwrap();
    let new = from_bincode(&to_bincode(&num).unwrap()).unwrap();

    assert_eq!(num, new);
  }

  /// Check that we can serialize zero to `bincode` and back.
  #[test]
  fn serialize_deserialize_bincode_zero() {
    let num = Num::from(0usize);
    let new = from_bincode(&to_bincode(&num).unwrap()).unwrap();

    assert_eq!(num, new);
  }
}
