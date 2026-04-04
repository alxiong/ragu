//! Internal implementation of the recursive verifier — circuits, proof
//! components, and claim-building machinery.
//!
//! # Submodules
//!
//! - [`native`] — circuits and types for the native (host) curve
//! - [`nested`] — circuits and types for the nested curve
//! - [`claims`] — shared claim-building abstraction used by both curves
//! - [`fold_revdot`], [`endoscalar`], [`suffix`], [`transcript`] —
//!   supporting gadgets and helpers

pub mod claims;
pub mod const_fns;
pub mod endoscalar;
pub mod fold_revdot;
pub mod native;
pub mod nested;
pub mod suffix;
pub mod transcript;

/// Identifies which of the two child proofs a component came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Side {
    Left,
    Right,
}

#[cfg(test)]
pub mod tests;
