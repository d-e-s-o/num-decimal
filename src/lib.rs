// Copyright (C) 2019-2023 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_unit_value, clippy::unreadable_literal)]
#![warn(
  bad_style,
  broken_intra_doc_links,
  dead_code,
  future_incompatible,
  illegal_floating_point_literal_pattern,
  improper_ctypes,
  late_bound_lifetime_arguments,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  no_mangle_generic_items,
  non_shorthand_field_patterns,
  nonstandard_style,
  overflowing_literals,
  path_statements,
  patterns_in_fns_without_body,
  private_in_public,
  proc_macro_derive_resolution_fallback,
  renamed_and_removed_lints,
  rust_2018_compatibility,
  rust_2018_idioms,
  stable_features,
  trivial_bounds,
  trivial_numeric_casts,
  type_alias_bounds,
  tyvar_behind_raw_pointer,
  unconditional_recursion,
  unreachable_code,
  unreachable_patterns,
  unstable_features,
  unstable_name_collisions,
  unused,
  unused_comparisons,
  unused_import_braces,
  unused_lifetimes,
  unused_qualifications,
  unused_results,
  where_clauses_object_safety,
  while_true
)]

//! A crate containing a number type suitable for use in financial
//! contexts.

#[cfg(all(feature = "num-v02", feature = "num-v04"))]
compile_error!("Only one of the features 'num-v02' and 'num-v04' can be enabled");

#[cfg(feature = "num-v02")]
pub use num_bigint_v02 as num_bigint;
#[cfg(feature = "num-v04")]
pub use num_bigint_v04 as num_bigint;
#[cfg(feature = "num-v02")]
pub use num_rational_v02 as num_rational;
#[cfg(feature = "num-v04")]
pub use num_rational_v04 as num_rational;

mod num;
#[cfg(feature = "serde")]
mod ser;

pub use crate::num::CustomDisplay;
pub use crate::num::Num;
pub use crate::num::Num32;
pub use crate::num::Num64;
pub use crate::num::ParseNumError;
