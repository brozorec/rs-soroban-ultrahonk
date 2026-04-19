use soroban_sdk::{
    crypto::bn254::Fr as SdkFr,
    BytesN, Env, U256,
};
use core::ops::{Add, Mul, Neg, Sub};
use hex;

#[cfg(not(feature = "std"))]
use alloc::{borrow::ToOwned, string::String};

#[inline(always)]
fn normalize_hex(s: &str) -> String {
    let raw = s.trim_start_matches("0x");
    if raw.len() & 1 == 1 {
        let mut out = String::with_capacity(raw.len() + 1);
        out.push('0');
        out.push_str(raw);
        out
    } else {
        raw.to_owned()
    }
}

/// BN254 scalar field element, wrapping the SDK's host-function-backed `Fr`.
/// All arithmetic is dispatched to CAP-0080 host functions (`bn254_fr_add`, etc).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fr(pub SdkFr);

impl Fr {
    pub fn from_u64(env: &Env, x: u64) -> Self {
        Fr(SdkFr::from_u256(U256::from_u128(env, x as u128)))
    }

    /// Construct from hex string (with or without 0x prefix).
    pub fn from_str(env: &Env, s: &str) -> Self {
        let bytes = hex::decode(normalize_hex(s)).expect("hex decode failed");
        let mut padded = [0u8; 32];
        let offset = 32 - bytes.len();
        padded[offset..].copy_from_slice(&bytes);
        Self::from_bytes(env, &padded)
    }

    /// Construct from a 32-byte big-endian array.
    pub fn from_bytes(env: &Env, bytes: &[u8; 32]) -> Self {
        Fr(SdkFr::from_bytes(BytesN::from_array(env, bytes)))
    }

    /// Convert to 32-byte big-endian representation.
    #[inline(always)]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes().to_array()
    }

    pub fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(Fr(self.0.inv()))
        }
    }

    pub fn zero(env: &Env) -> Self {
        Fr(SdkFr::from_u256(U256::from_u32(env, 0)))
    }

    pub fn one(env: &Env) -> Self {
        Fr(SdkFr::from_u256(U256::from_u32(env, 1)))
    }

    pub fn pow(&self, exp: u64) -> Self {
        Fr(self.0.pow(exp))
    }

    pub fn is_zero(&self) -> bool {
        let env = self.0.env();
        *self == Fr::zero(env)
    }
}

/// Montgomery batch inversion: compute all inverses of `vals[..n]` using a
/// single field inversion + 3*(n-1) multiplications, writing results into `out`.
/// Both `vals` and `out` must have the same length.
/// Returns an error if any element is zero (the product is non-invertible).
pub fn batch_inverse(vals: &[Fr], out: &mut [Fr]) -> Result<(), &'static str> {
    let n = vals.len();
    assert_eq!(n, out.len(), "batch_inverse: len mismatch");

    if n == 0 {
        return Ok(());
    }

    // 1) Build prefix products in `out`: out[i] = vals[0] * vals[1] * ... * vals[i]
    out[0] = vals[0].clone();
    for i in 1..n {
        out[i] = out[i - 1].clone() * vals[i].clone();
    }

    // 2) Invert the total product
    let mut inv_acc = out[n - 1]
        .inverse()
        .ok_or("batch_inverse: product is zero (at least one input element is zero)")?;

    // 3) Sweep back to recover individual inverses
    for i in (1..n).rev() {
        out[i] = inv_acc.clone() * out[i - 1].clone();
        inv_acc = inv_acc * vals[i].clone();
    }
    out[0] = inv_acc;
    Ok(())
}

impl Add for Fr {
    type Output = Fr;
    fn add(self, rhs: Fr) -> Fr {
        Fr(self.0 + rhs.0)
    }
}

impl Sub for Fr {
    type Output = Fr;
    fn sub(self, rhs: Fr) -> Fr {
        Fr(self.0 - rhs.0)
    }
}

impl Mul for Fr {
    type Output = Fr;
    fn mul(self, rhs: Fr) -> Fr {
        Fr(self.0 * rhs.0)
    }
}

impl Neg for Fr {
    type Output = Fr;
    fn neg(self) -> Fr {
        Fr::zero(self.0.env()) - self
    }
}
