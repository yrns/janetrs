//! Module for stuff that are not required either to use in a application or to write
//! janet modules.
use core::fmt;

use crate::types::Janet;

pub use janetrs_version::{JanetBuildConfig, JanetVersion};

/// Checks if the given `args` have the same amount of expected arguments, if the check
/// fails it panics from the Janet side.
#[inline]
pub fn check_fix_arity(args: &[Janet], fix_arity: usize) {
    if args.len() != fix_arity {
        crate::jpanic!("arity mismatch, expected {}, got {}", fix_arity, args.len());
    }
}

/// Check if the given `args` have the expected arguments in the inclusive range, if the
/// check fails it panics from the Janet side.
///
/// If `max` is `None`, it will disable the maximum check, allowing variadic arguments.
#[inline]
pub fn check_range_arity(args: &[Janet], min: usize, max: Option<usize>) {
    let arity = args.len();

    if arity < min {
        crate::jpanic!("arity mismatch, expected at least {}, got {}", min, arity);
    }

    if let Some(max) = max {
        if arity > max {
            crate::jpanic!("arity mismatch, expected at most {}, got {}", max, arity);
        }
    }
}

/// Just a wrapper for the janet panic function
#[doc(hidden)]
#[inline]
pub fn _panic(msg: Janet) -> ! {
    unsafe { evil_janet::janet_panicv(msg.inner) }
}

#[doc(hidden)]
#[allow(dead_code)]
#[track_caller]
pub fn assert_deep_inner(
    op: &'static str,
    left: &dyn fmt::Debug,
    right: &dyn fmt::Debug,
    args: Option<fmt::Arguments<'_>>,
) -> ! {
    match args {
        Some(args) => panic!(
            r#"assertion `left {op} right` failed: {args}
  left: {left:?}
 right: {right:?}"#
        ),
        None => panic!(
            r#"assertion `left {op} right` failed
  left: {left:?}
 right: {right:?}"#
        ),
    }
}
