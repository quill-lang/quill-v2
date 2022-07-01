//! Feather's kernel.
//!
//! This is heavily inspired by the Lean 3 kernel: <https://github.com/leanprover/lean/blob/master/src/kernel>.

#![feature(let_chains)]

// Expose this either when we're running `cargo doc` or executing tests.
#[cfg(any(test, doc))]
mod test_db;

pub mod expr;
pub mod typeck;
pub mod universe;
