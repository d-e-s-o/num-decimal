// Copyright (C) 2021 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fmt::Formatter;
use std::fmt::Result as FmtResult;
use std::str::FromStr as _;

use serde::de::Error;
use serde::de::Unexpected;
use serde::de::Visitor;
use serde::Deserialize;
use serde::Deserializer;
use serde::Serialize;
use serde::Serializer;

use crate::Num;


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

    deserializer.deserialize_any(HumanReadable)
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


#[cfg(test)]
mod tests {
  use super::*;

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
}
