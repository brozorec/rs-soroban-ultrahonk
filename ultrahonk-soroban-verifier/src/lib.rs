#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

pub mod debug;
pub mod ec;
pub mod field;
pub mod hash;
pub mod relations;
pub mod shplemini;
pub mod sumcheck;
pub mod transcript;
pub mod types;
pub mod utils;
pub mod verifier;
/// Number of 32-byte fields in a compact proof (G1 points stored as 2 fields
/// instead of BB's 4-field limb-split encoding).
pub const PROOF_FIELDS: usize = 382;
pub const PROOF_BYTES: usize = PROOF_FIELDS * 32;

/// BB's native proof dimensions (limb-split G1 encoding: 4 × 32 B per point).
/// Use [`utils::compact_proof`] to convert from BB format to compact format.
pub const BB_PROOF_FIELDS: usize = 456;
pub const BB_PROOF_BYTES: usize = BB_PROOF_FIELDS * 32;

pub use verifier::UltraHonkVerifier;
