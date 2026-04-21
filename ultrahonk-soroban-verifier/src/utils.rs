//! Utilities for loading Proof and VerificationKey, plus byte↔field/point conversion.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::field::Fr;
use crate::types::{
    G1Point, Proof, VerificationKey, BATCHED_RELATION_PARTIAL_LENGTH, CONST_PROOF_SIZE_LOG_N,
    NUMBER_OF_ENTITIES, PAIRING_POINTS_SIZE,
};
use crate::{BB_PROOF_BYTES, PROOF_BYTES};
use core::array;
use soroban_sdk::{Bytes, Env};

/// Split a 32-byte big-endian field element into (low136, high) limbs.
pub fn coord_to_halves_be(coord: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
    let mut low = [0u8; 32];
    let mut high = [0u8; 32];
    low[15..].copy_from_slice(&coord[15..]); // 17 bytes
    high[17..].copy_from_slice(&coord[..15]); // 15 bytes
    (low, high)
}

fn read_bytes<const N: usize>(bytes: &Bytes, idx: &mut u32) -> [u8; N] {
    let mut out = [0u8; N];
    let end = *idx + N as u32;
    bytes.slice(*idx..end).copy_into_slice(&mut out);
    *idx = end;
    out
}

fn combine_limbs(lo: &[u8; 32], hi: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..15].copy_from_slice(&hi[17..]);
    out[15..].copy_from_slice(&lo[15..]);
    out
}

fn bytes_to_g1_proof_point(bytes: &Bytes, cur: &mut u32) -> G1Point {
    let x = read_bytes::<32>(bytes, cur);
    let y = read_bytes::<32>(bytes, cur);
    G1Point { x, y }
}

fn bytes_to_fr(env: &Env, bytes: &Bytes, cur: &mut u32) -> Fr {
    let arr = read_bytes::<32>(bytes, cur);
    Fr::from_bytes(env, &arr)
}

/// Load a Proof from a compact byte array (see [`compact_proof`]).
///
/// G1 points are stored as two 32-byte coordinates (x, y) = 64 bytes each.
/// BB's native format uses a 4×32 limb-split encoding; call [`compact_proof`]
/// to convert BB output before passing it here.
pub fn load_proof(proof_bytes: &Bytes) -> Proof {
    assert_eq!(proof_bytes.len() as usize, PROOF_BYTES, "proof bytes len");
    let env = proof_bytes.env();
    let mut boundary = 0u32;

    // 0) pairing point object
    let pairing_point_object: [Fr; PAIRING_POINTS_SIZE] =
        array::from_fn(|_| bytes_to_fr(env, proof_bytes, &mut boundary));

    // 1) w1, w2, w3
    let w1 = bytes_to_g1_proof_point(proof_bytes, &mut boundary);
    let w2 = bytes_to_g1_proof_point(proof_bytes, &mut boundary);
    let w3 = bytes_to_g1_proof_point(proof_bytes, &mut boundary);

    // 2) lookup_read_counts, lookup_read_tags
    let lookup_read_counts = bytes_to_g1_proof_point(proof_bytes, &mut boundary);
    let lookup_read_tags = bytes_to_g1_proof_point(proof_bytes, &mut boundary);

    // 3) w4
    let w4 = bytes_to_g1_proof_point(proof_bytes, &mut boundary);

    // 4) lookup_inverses, z_perm
    let lookup_inverses = bytes_to_g1_proof_point(proof_bytes, &mut boundary);
    let z_perm = bytes_to_g1_proof_point(proof_bytes, &mut boundary);

    // 5) sumcheck_univariates
    let sumcheck_univariates: [[Fr; BATCHED_RELATION_PARTIAL_LENGTH]; CONST_PROOF_SIZE_LOG_N] =
        array::from_fn(|_| {
            array::from_fn(|_| bytes_to_fr(env, proof_bytes, &mut boundary))
        });

    // 6) sumcheck_evaluations
    let sumcheck_evaluations: [Fr; NUMBER_OF_ENTITIES] =
        array::from_fn(|_| bytes_to_fr(env, proof_bytes, &mut boundary));

    // 7) gemini_fold_comms
    let gemini_fold_comms: [G1Point; CONST_PROOF_SIZE_LOG_N - 1] =
        array::from_fn(|_| bytes_to_g1_proof_point(proof_bytes, &mut boundary));

    // 8) gemini_a_evaluations
    let gemini_a_evaluations: [Fr; CONST_PROOF_SIZE_LOG_N] =
        array::from_fn(|_| bytes_to_fr(env, proof_bytes, &mut boundary));

    // 9) shplonk_q, kzg_quotient
    let shplonk_q = bytes_to_g1_proof_point(proof_bytes, &mut boundary);
    let kzg_quotient = bytes_to_g1_proof_point(proof_bytes, &mut boundary);

    Proof {
        pairing_point_object,
        w1,
        w2,
        w3,
        w4,
        lookup_read_counts,
        lookup_read_tags,
        lookup_inverses,
        z_perm,
        sumcheck_univariates,
        sumcheck_evaluations,
        gemini_fold_comms,
        gemini_a_evaluations,
        shplonk_q,
        kzg_quotient,
    }
}

/// Load a VerificationKey.
pub fn load_vk_from_bytes(bytes: &Bytes) -> Option<VerificationKey> {
    const HEADER_WORDS: usize = 4;
    const NUM_POINTS: usize = 27;
    const EXPECTED_LEN: usize = HEADER_WORDS * 8 + NUM_POINTS * 64;
    if bytes.len() as usize != EXPECTED_LEN {
        return None;
    }

    let mut idx = 0u32;
    let circuit_size = u64::from_be_bytes(read_bytes::<8>(bytes, &mut idx));
    let log_circuit_size = u64::from_be_bytes(read_bytes::<8>(bytes, &mut idx));
    let public_inputs_size = u64::from_be_bytes(read_bytes::<8>(bytes, &mut idx));
    let _pub_inputs_offset = u64::from_be_bytes(read_bytes::<8>(bytes, &mut idx));

    fn read_point(bytes: &Bytes, idx: &mut u32) -> Option<G1Point> {
        let x = read_bytes::<32>(bytes, idx);
        let y = read_bytes::<32>(bytes, idx);
        Some(G1Point { x, y })
    }

    let qm = read_point(bytes, &mut idx)?;
    let qc = read_point(bytes, &mut idx)?;
    let ql = read_point(bytes, &mut idx)?;
    let qr = read_point(bytes, &mut idx)?;
    let qo = read_point(bytes, &mut idx)?;
    let q4 = read_point(bytes, &mut idx)?;
    let q_lookup = read_point(bytes, &mut idx)?;
    let q_arith = read_point(bytes, &mut idx)?;
    let q_delta_range = read_point(bytes, &mut idx)?;
    let q_elliptic = read_point(bytes, &mut idx)?;
    let q_aux = read_point(bytes, &mut idx)?;
    let q_poseidon2_external = read_point(bytes, &mut idx)?;
    let q_poseidon2_internal = read_point(bytes, &mut idx)?;
    let s1 = read_point(bytes, &mut idx)?;
    let s2 = read_point(bytes, &mut idx)?;
    let s3 = read_point(bytes, &mut idx)?;
    let s4 = read_point(bytes, &mut idx)?;
    let id1 = read_point(bytes, &mut idx)?;
    let id2 = read_point(bytes, &mut idx)?;
    let id3 = read_point(bytes, &mut idx)?;
    let id4 = read_point(bytes, &mut idx)?;
    let t1 = read_point(bytes, &mut idx)?;
    let t2 = read_point(bytes, &mut idx)?;
    let t3 = read_point(bytes, &mut idx)?;
    let t4 = read_point(bytes, &mut idx)?;
    let lagrange_first = read_point(bytes, &mut idx)?;
    let lagrange_last = read_point(bytes, &mut idx)?;

    Some(VerificationKey {
        circuit_size,
        log_circuit_size,
        public_inputs_size,
        qm,
        qc,
        ql,
        qr,
        qo,
        q4,
        q_lookup,
        q_arith,
        q_delta_range,
        q_elliptic,
        q_aux,
        q_poseidon2_external,
        q_poseidon2_internal,
        s1,
        s2,
        s3,
        s4,
        id1,
        id2,
        id3,
        id4,
        t1,
        t2,
        t3,
        t4,
        lagrange_first,
        lagrange_last,
    })
}

/// Convert a BB-format proof (limb-split G1 points, 14592 bytes) into compact
/// format (full 32-byte coordinates, 12224 bytes).
///
/// BB encodes each G1 coordinate as two 32-byte limbs (lo136, hi118).
/// This function combines each pair into a single 32-byte big-endian value,
/// halving the per-point footprint from 128 to 64 bytes. Field elements (Fr)
/// are already 32 bytes and are copied unchanged.
pub fn compact_proof(bb_proof: &[u8]) -> Vec<u8> {
    assert_eq!(bb_proof.len(), BB_PROOF_BYTES, "expected BB proof length");

    struct Compactor<'a> {
        src: &'a [u8],
        out: Vec<u8>,
        pos: usize,
    }

    impl<'a> Compactor<'a> {
        fn copy_fr(&mut self, n: usize) {
            let bytes = n * 32;
            self.out.extend_from_slice(&self.src[self.pos..self.pos + bytes]);
            self.pos += bytes;
        }

        fn compact_g1(&mut self) {
            let p = self.pos;
            self.out.extend_from_slice(&combine_limbs(
                self.src[p..p + 32].try_into().unwrap(),
                self.src[p + 32..p + 64].try_into().unwrap(),
            ));
            self.out.extend_from_slice(&combine_limbs(
                self.src[p + 64..p + 96].try_into().unwrap(),
                self.src[p + 96..p + 128].try_into().unwrap(),
            ));
            self.pos += 128;
        }
    }

    let mut c = Compactor { src: bb_proof, out: Vec::with_capacity(PROOF_BYTES), pos: 0 };

    c.copy_fr(16);                                             // pairing_point_object
    for _ in 0..3 { c.compact_g1(); }                         // w1, w2, w3
    for _ in 0..2 { c.compact_g1(); }                         // lookup_read_counts, lookup_read_tags
    c.compact_g1();                                             // w4
    for _ in 0..2 { c.compact_g1(); }                         // lookup_inverses, z_perm
    c.copy_fr(BATCHED_RELATION_PARTIAL_LENGTH * CONST_PROOF_SIZE_LOG_N); // sumcheck_univariates
    c.copy_fr(NUMBER_OF_ENTITIES);                             // sumcheck_evaluations
    for _ in 0..CONST_PROOF_SIZE_LOG_N - 1 { c.compact_g1(); } // gemini_fold_comms
    c.copy_fr(CONST_PROOF_SIZE_LOG_N);                         // gemini_a_evaluations
    for _ in 0..2 { c.compact_g1(); }                         // shplonk_q, kzg_quotient

    debug_assert_eq!(c.pos, BB_PROOF_BYTES);
    debug_assert_eq!(c.out.len(), PROOF_BYTES);
    c.out
}
