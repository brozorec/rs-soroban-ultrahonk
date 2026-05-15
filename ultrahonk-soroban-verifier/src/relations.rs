//!
//! This module accumulates all of the UltraHonk relations (arithmetic, permutation,
//! lookup, range, elliptic, auxiliary, Poseidon external/internal) into a single
//! scalar which is then batched with the alpha challenges.

use crate::field::Fr;
use crate::types::{RelationParameters, Wire, NUMBER_OF_SUBRELATIONS};
use soroban_sdk::Env;

#[cfg(feature = "std")]
macro_rules! println {
    ($($args:tt)*) => { std::println!($($args)*) };
}

/// Precomputed NEG_HALF = (p - 1)/2 in BN254 scalar field.
fn neg_half(env: &Env) -> Fr {
    Fr::from_str(env, "0x183227397098d014dc2822db40c0ac2e9419f4243cdcb848a1f0fac9f8000000")
}

/// Internal matrix diagonal values for Poseidon hash
fn internal_matrix_diagonal(env: &Env) -> [Fr; 4] {
    [
        Fr::from_str(env, "0x10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e7"),
        Fr::from_str(env, "0x0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740b"),
        Fr::from_str(env, "0x00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac15"),
        Fr::from_str(env, "0x222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428b"),
    ]
}

/// Helper to borrow a wire value from the eval array.
#[inline(always)]
fn w(vals: &[Fr], wr: Wire) -> &Fr {
    &vals[wr.index()]
}

/// Accumulate the two arithmetic subrelations (indices 0 and 1).
fn accumulate_arithmetic_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: &Fr) {
    // Relation 0
    {
        let q_arith = w(p, Wire::QArith);
        let neg_half = neg_half(env);
        let mut accum = (q_arith - Fr::from_u64(env, 3))
            * w(p, Wire::Qm)
            * w(p, Wire::Wr)
            * w(p, Wire::Wl)
            * neg_half;
        accum = accum
            + w(p, Wire::Ql) * w(p, Wire::Wl)
            + w(p, Wire::Qr) * w(p, Wire::Wr)
            + w(p, Wire::Qo) * w(p, Wire::Wo)
            + w(p, Wire::Q4) * w(p, Wire::W4)
            + w(p, Wire::Qc);
        accum = (accum + (q_arith - Fr::one(env)) * w(p, Wire::W4Shift)) * q_arith * domain_sep;
        evals[0] = accum;
    }
    // Relation 1
    {
        let q_arith = w(p, Wire::QArith);
        let mut accum =
            w(p, Wire::Wl) + w(p, Wire::W4) - w(p, Wire::WlShift) + w(p, Wire::Qm);
        accum = accum
            * (q_arith - Fr::from_u64(env, 2))
            * (q_arith - Fr::from_u64(env, 1))
            * q_arith
            * domain_sep;
        evals[1] = accum;
    }
}

/// Accumulate the two permutation subrelations (indices 2 and 3).
fn accumulate_permutation_relation(
    p: &[Fr],
    rp: &RelationParameters,
    evals: &mut [Fr],
    domain_sep: &Fr,
) {
    let beta = &rp.beta;
    let gamma = &rp.gamma;

    let grand_product_numerator = (w(p, Wire::Wl) + w(p, Wire::Id1) * beta + gamma)
        * (w(p, Wire::Wr) + w(p, Wire::Id2) * beta + gamma)
        * (w(p, Wire::Wo) + w(p, Wire::Id3) * beta + gamma)
        * (w(p, Wire::W4) + w(p, Wire::Id4) * beta + gamma);

    let grand_product_denominator = (w(p, Wire::Wl) + w(p, Wire::Sigma1) * beta + gamma)
        * (w(p, Wire::Wr) + w(p, Wire::Sigma2) * beta + gamma)
        * (w(p, Wire::Wo) + w(p, Wire::Sigma3) * beta + gamma)
        * (w(p, Wire::W4) + w(p, Wire::Sigma4) * beta + gamma);

    // Contribution 2
    evals[2] = ((w(p, Wire::ZPerm) + w(p, Wire::LagrangeFirst)) * grand_product_numerator
        - (w(p, Wire::ZPermShift) + w(p, Wire::LagrangeLast) * &rp.public_inputs_delta)
            * grand_product_denominator)
        * domain_sep;

    // Contribution 3
    evals[3] = w(p, Wire::LagrangeLast) * w(p, Wire::ZPermShift) * domain_sep;
}

/// Accumulate the two lookup log-derivative subrelations (indices 4 and 5).
fn accumulate_log_derivative_lookup_relation(
    p: &[Fr],
    rp: &RelationParameters,
    evals: &mut [Fr],
    domain_sep: &Fr,
) {
    let eta = &rp.eta;
    let eta_two = &rp.eta_two;
    let eta_three = &rp.eta_three;
    let gamma = &rp.gamma;

    let write_term = w(p, Wire::Table1)
        + gamma
        + w(p, Wire::Table2) * eta
        + w(p, Wire::Table3) * eta_two
        + w(p, Wire::Table4) * eta_three;

    let derived_entry_2 = w(p, Wire::Wr) + w(p, Wire::Qm) * w(p, Wire::WrShift);
    let derived_entry_3 = w(p, Wire::Wo) + w(p, Wire::Qc) * w(p, Wire::WoShift);

    let read_term = w(p, Wire::Wl)
        + gamma
        + w(p, Wire::Qr) * w(p, Wire::WlShift)
        + derived_entry_2 * eta
        + derived_entry_3 * eta_two
        + w(p, Wire::Qo) * eta_three;

    let inv = w(p, Wire::LookupInverses);
    let inv_exists = w(p, Wire::LookupReadTags) + w(p, Wire::QLookup)
        - w(p, Wire::LookupReadTags) * w(p, Wire::QLookup);

    evals[4] = (&read_term * &write_term * inv - inv_exists) * domain_sep;
    evals[5] = w(p, Wire::QLookup) * (write_term * inv)
        - w(p, Wire::LookupReadCounts) * (read_term * inv);
}

/// Accumulate the four range-check subrelations (indices 6..9).
fn accumulate_delta_range_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: &Fr) {
    let zero = Fr::zero(env);
    let minus_one = &zero - Fr::from_u64(env, 1);
    let minus_two = &zero - Fr::from_u64(env, 2);
    let minus_three = &zero - Fr::from_u64(env, 3);

    let deltas = [
        w(p, Wire::Wr) - w(p, Wire::Wl),
        w(p, Wire::Wo) - w(p, Wire::Wr),
        w(p, Wire::W4) - w(p, Wire::Wo),
        w(p, Wire::WlShift) - w(p, Wire::W4),
    ];
    let negs = [minus_one, minus_two, minus_three];

    // Contributions 6..9
    for i in 0..4 {
        let mut acc = deltas[i].clone();
        for n in &negs {
            acc = acc * (&deltas[i] + n);
        }
        evals[6 + i] = acc * w(p, Wire::QRange) * domain_sep;
    }
}

/// Accumulate elliptic-curve subrelations (indices 10..11).
fn accumulate_elliptic_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: &Fr) {
    let x1 = w(p, Wire::Wr);
    let y1 = w(p, Wire::Wo);
    let x2 = w(p, Wire::WlShift);
    let y2 = w(p, Wire::W4Shift);
    let x3 = w(p, Wire::WrShift);
    let y3 = w(p, Wire::WoShift);

    let q_sign = w(p, Wire::Ql);
    let q_double = w(p, Wire::Qm);
    let q_gate = w(p, Wire::QElliptic);

    let delta_x = x2 - x1;
    let y1_sq = y1 * y1;

    let x_add_id = {
        let y2_sq = y2 * y2;
        let y1y2 = y1 * y2 * q_sign;
        (x3 + x2 + x1) * &delta_x * &delta_x - y2_sq - &y1_sq + &y1y2 + y1y2
    };
    let y_add_id = {
        let y_diff = y2 * q_sign - y1;
        (y1 + y3) * delta_x + (x3 - x1) * y_diff
    };

    let b_neg = Fr::from_u64(env, 17);

    let x_double_id = {
        let x_pow_4 = (&y1_sq + b_neg) * x1;
        let y1_sqr_mul_4 = &y1_sq + &y1_sq + &y1_sq + y1_sq;
        let x_pow_4_mul_9 = x_pow_4 * Fr::from_u64(env, 9);
        (x3 + x1 + x1) * y1_sqr_mul_4 - x_pow_4_mul_9
    };
    let y_double_id = {
        let x1_sqr_mul_3 = (x1 + x1 + x1) * x1;
        x1_sqr_mul_3 * (x1 - x3) - (y1 + y1) * (y1 + y3)
    };

    let add_factor = (Fr::one(env) - q_double) * q_gate * domain_sep;
    let double_factor = q_double * q_gate * domain_sep;

    // Contribution 10: elliptic x
    evals[10] = x_add_id * &add_factor + x_double_id * &double_factor;
    // Contribution 11: elliptic y
    evals[11] = y_add_id * add_factor + y_double_id * double_factor;
}

/// Accumulate auxiliary subrelations (indices 12..17).
fn accumulate_auxillary_relation(
    env: &Env,
    p: &[Fr],
    rp: &RelationParameters,
    evals: &mut [Fr],
    domain_sep: &Fr,
) {
    let ls = Fr::from_str(env, "0x100000000000000000");
    let ss = Fr::from_u64(env, 1 << 14);
    let one = Fr::one(env);
    let eta = &rp.eta;
    let eta_two = &rp.eta_two;
    let eta_three = &rp.eta_three;

    let mut limb_subproduct =
        w(p, Wire::Wl) * w(p, Wire::WrShift) + w(p, Wire::WlShift) * w(p, Wire::Wr);

    let mut non_native_field_gate_2 = w(p, Wire::Wl) * w(p, Wire::W4)
        + w(p, Wire::Wr) * w(p, Wire::Wo)
        - w(p, Wire::WoShift);
    non_native_field_gate_2 =
        non_native_field_gate_2 * &ls - w(p, Wire::W4Shift) + &limb_subproduct;
    non_native_field_gate_2 = non_native_field_gate_2 * w(p, Wire::Q4);

    limb_subproduct = limb_subproduct * ls + w(p, Wire::WlShift) * w(p, Wire::WrShift);

    let non_native_field_gate_1 =
        (&limb_subproduct - (w(p, Wire::Wo) + w(p, Wire::W4))) * w(p, Wire::Qo);

    let non_native_field_gate_3 = (&limb_subproduct + w(p, Wire::W4)
        - (w(p, Wire::WoShift) + w(p, Wire::W4Shift)))
        * w(p, Wire::Qm);

    let non_native_field_identity =
        (non_native_field_gate_1 + non_native_field_gate_2 + non_native_field_gate_3)
            * w(p, Wire::Qr);

    let mut limb_accumulator_1 = w(p, Wire::WrShift) * &ss + w(p, Wire::WlShift);
    limb_accumulator_1 = limb_accumulator_1 * &ss + w(p, Wire::Wo);
    limb_accumulator_1 = limb_accumulator_1 * &ss + w(p, Wire::Wr);
    limb_accumulator_1 = limb_accumulator_1 * &ss + w(p, Wire::Wl);
    limb_accumulator_1 = (limb_accumulator_1 - w(p, Wire::W4)) * w(p, Wire::Q4);

    let mut limb_accumulator_2 = w(p, Wire::WoShift) * &ss + w(p, Wire::WrShift);
    limb_accumulator_2 = limb_accumulator_2 * &ss + w(p, Wire::WlShift);
    limb_accumulator_2 = limb_accumulator_2 * &ss + w(p, Wire::W4);
    limb_accumulator_2 = limb_accumulator_2 * ss + w(p, Wire::Wo);
    limb_accumulator_2 = (limb_accumulator_2 - w(p, Wire::W4Shift)) * w(p, Wire::Qm);

    let limb_accumulator_identity = (limb_accumulator_1 + limb_accumulator_2) * w(p, Wire::Qo);

    let partial_record_check = w(p, Wire::Wo) * eta_three
        + w(p, Wire::Wr) * eta_two
        + w(p, Wire::Wl) * eta
        + w(p, Wire::Qc);
    let memory_record_check = &partial_record_check - w(p, Wire::W4);

    let index_delta = w(p, Wire::WlShift) - w(p, Wire::Wl);
    let record_delta = w(p, Wire::W4Shift) - w(p, Wire::W4);

    let index_is_monotonically_increasing = &index_delta * &index_delta - &index_delta;
    let adjacent_values_match_if_adjacent_indices_match = (&one - &index_delta) * record_delta;

    evals[13] = adjacent_values_match_if_adjacent_indices_match
        * w(p, Wire::Ql)
        * w(p, Wire::Qr)
        * w(p, Wire::QAux)
        * domain_sep;
    // Contribution 14: ROM index monotonic
    evals[14] = &index_is_monotonically_increasing
        * w(p, Wire::Ql)
        * w(p, Wire::Qr)
        * w(p, Wire::QAux)
        * domain_sep;

    let access_type = w(p, Wire::W4) - &partial_record_check;
    let access_check = &access_type * &access_type - access_type;

    let next_gate_access_type_sum = w(p, Wire::WoShift) * eta_three
        + w(p, Wire::WrShift) * eta_two
        + w(p, Wire::WlShift) * eta;
    let next_gate_access_type = w(p, Wire::W4Shift) - next_gate_access_type_sum;

    let value_delta = w(p, Wire::WoShift) - w(p, Wire::Wo);
    let adjacent_values_match_if_adjacent_indices_match_and_next_access_is_a_read_operation =
        (&one - &index_delta) * value_delta * (&one - &next_gate_access_type);

    // Contribution 15,16,17: RAM
    evals[15] = adjacent_values_match_if_adjacent_indices_match_and_next_access_is_a_read_operation
        * w(p, Wire::QArith)
        * w(p, Wire::QAux)
        * domain_sep;
    evals[16] = index_is_monotonically_increasing
        * w(p, Wire::QArith)
        * w(p, Wire::QAux)
        * domain_sep;
    evals[17] = (&next_gate_access_type * &next_gate_access_type - next_gate_access_type)
        * w(p, Wire::QArith)
        * w(p, Wire::QAux)
        * domain_sep;

    let rom_consistency_check_identity =
        &memory_record_check * w(p, Wire::Ql) * w(p, Wire::Qr);
    let ram_timestamp_check_identity = (one - index_delta)
        * (w(p, Wire::WrShift) - w(p, Wire::Wr))
        - w(p, Wire::Wo);
    let ram_consistency_check_identity = access_check * w(p, Wire::QArith);

    let memory_identity = rom_consistency_check_identity
        + ram_timestamp_check_identity * w(p, Wire::Q4) * w(p, Wire::Ql)
        + memory_record_check * w(p, Wire::Qm) * w(p, Wire::Ql)
        + ram_consistency_check_identity;

    let auxiliary_identity =
        memory_identity + non_native_field_identity + limb_accumulator_identity;
    // Contribution 12
    evals[12] = auxiliary_identity * w(p, Wire::QAux) * domain_sep;
}

/// Accumulate Poseidon external subrelations (indices 18..21).
fn accumulate_poseidon_external_relation(p: &[Fr], evals: &mut [Fr], domain_sep: &Fr) {
    let s1 = w(p, Wire::Wl) + w(p, Wire::Ql);
    let s2 = w(p, Wire::Wr) + w(p, Wire::Qr);
    let s3 = w(p, Wire::Wo) + w(p, Wire::Qo);
    let s4 = w(p, Wire::W4) + w(p, Wire::Q4);

    let u1_ext = s1.pow(5);
    let u2_ext = s2.pow(5);
    let u3_ext = s3.pow(5);
    let u4_ext = s4.pow(5);

    let t0 = &u1_ext + &u2_ext;
    let t1 = &u3_ext + &u4_ext;
    let t2 = &u2_ext + &u2_ext + &t1;
    let t3 = &u4_ext + &u4_ext + &t0;

    let v4 = &t1 + &t1 + &t1 + t1 + &t3;
    let v2 = &t0 + &t0 + &t0 + t0 + &t2;
    let v1 = t3 + &v2;
    let v3 = t2 + &v4;

    let q_poseidon = w(p, Wire::QPoseidon2External);
    evals[18] = (v1 - w(p, Wire::WlShift)) * q_poseidon * domain_sep;
    evals[19] = (v2 - w(p, Wire::WrShift)) * q_poseidon * domain_sep;
    evals[20] = (v3 - w(p, Wire::WoShift)) * q_poseidon * domain_sep;
    evals[21] = (v4 - w(p, Wire::W4Shift)) * q_poseidon * domain_sep;
}

/// Accumulate Poseidon internal subrelations (indices 22..25).
fn accumulate_poseidon_internal_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: &Fr) {
    let u1_int = (w(p, Wire::Wl) + w(p, Wire::Ql)).pow(5);
    let u2_int = w(p, Wire::Wr);
    let u3_int = w(p, Wire::Wo);
    let u4_int = w(p, Wire::W4);
    let q_poseidon = w(p, Wire::QPoseidon2Internal);
    let u_sum = &u1_int + u2_int + u3_int + u4_int;
    let diag = internal_matrix_diagonal(env);

    let w1 = u1_int * &diag[0] + &u_sum;
    let w2 = u2_int * &diag[1] + &u_sum;
    let w3 = u3_int * &diag[2] + &u_sum;
    let w4 = u4_int * &diag[3] + u_sum;

    evals[22] = (w1 - w(p, Wire::WlShift)) * q_poseidon * domain_sep;
    evals[23] = (w2 - w(p, Wire::WrShift)) * q_poseidon * domain_sep;
    evals[24] = (w3 - w(p, Wire::WoShift)) * q_poseidon * domain_sep;
    evals[25] = (w4 - w(p, Wire::W4Shift)) * q_poseidon * domain_sep;
}

/// Batch all NUM_SUBRELATIONS = 26 subrelations with the alpha challenges.
fn scale_and_batch_subrelations(evaluations: &[Fr], subrelation_challenges: &[Fr]) -> Fr {
    let mut accumulator = evaluations[0].clone();
    for i in 1..NUMBER_OF_SUBRELATIONS {
        accumulator = accumulator + &evaluations[i] * &subrelation_challenges[i - 1];
    }
    accumulator
}

/// Main entrypoint: accumulate all subrelations and batch with alphas.
pub fn accumulate_relation_evaluations(
    env: &Env,
    purported_evaluations: &[Fr],
    rp: &RelationParameters,
    alphas: &[Fr],
    pow_partial_eval: Fr,
) -> Fr {
    let mut evaluations: [Fr; NUMBER_OF_SUBRELATIONS] =
        core::array::from_fn(|_| Fr::zero(env));

    let ds = &pow_partial_eval;
    accumulate_arithmetic_relation(env, purported_evaluations, &mut evaluations, ds);
    accumulate_permutation_relation(purported_evaluations, rp, &mut evaluations, ds);
    accumulate_log_derivative_lookup_relation(purported_evaluations, rp, &mut evaluations, ds);
    accumulate_delta_range_relation(env, purported_evaluations, &mut evaluations, ds);
    accumulate_elliptic_relation(env, purported_evaluations, &mut evaluations, ds);
    accumulate_auxillary_relation(env, purported_evaluations, rp, &mut evaluations, ds);
    accumulate_poseidon_external_relation(purported_evaluations, &mut evaluations, ds);
    accumulate_poseidon_internal_relation(env, purported_evaluations, &mut evaluations, ds);

    scale_and_batch_subrelations(&evaluations, alphas)
}
