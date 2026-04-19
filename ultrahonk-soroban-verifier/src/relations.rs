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

/// Helper to index into the wire array.
fn wire(vals: &[Fr], w: Wire) -> Fr {
    vals[w.index()].clone()
}

/// Accumulate the two arithmetic subrelations (indices 0 and 1).
fn accumulate_arithmetic_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: Fr) {
    // Relation 0
    {
        let q_arith = wire(p, Wire::QArith);
        let neg_half = neg_half(env);
        let mut accum = (q_arith.clone() - Fr::from_u64(env, 3))
            * wire(p, Wire::Qm)
            * wire(p, Wire::Wr)
            * wire(p, Wire::Wl)
            * neg_half;
        accum = accum
            + wire(p, Wire::Ql) * wire(p, Wire::Wl)
            + wire(p, Wire::Qr) * wire(p, Wire::Wr)
            + wire(p, Wire::Qo) * wire(p, Wire::Wo)
            + wire(p, Wire::Q4) * wire(p, Wire::W4)
            + wire(p, Wire::Qc);
        accum = (accum + (q_arith.clone() - Fr::one(env)) * wire(p, Wire::W4Shift)) * q_arith * domain_sep.clone();
        evals[0] = accum;
    }
    // Relation 1
    {
        let q_arith = wire(p, Wire::QArith);
        let mut accum =
            wire(p, Wire::Wl) + wire(p, Wire::W4) - wire(p, Wire::WlShift) + wire(p, Wire::Qm);
        accum = accum
            * (q_arith.clone() - Fr::from_u64(env, 2))
            * (q_arith.clone() - Fr::from_u64(env, 1))
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
    domain_sep: Fr,
) {
    let grand_product_numerator = {
        let mut num = wire(p, Wire::Wl) + wire(p, Wire::Id1) * rp.beta.clone() + rp.gamma.clone();
        num = num
            * (wire(p, Wire::Wr) + wire(p, Wire::Id2) * rp.beta.clone() + rp.gamma.clone())
            * (wire(p, Wire::Wo) + wire(p, Wire::Id3) * rp.beta.clone() + rp.gamma.clone())
            * (wire(p, Wire::W4) + wire(p, Wire::Id4) * rp.beta.clone() + rp.gamma.clone());
        num
    };

    let grand_product_denominator = {
        let mut den = wire(p, Wire::Wl) + wire(p, Wire::Sigma1) * rp.beta.clone() + rp.gamma.clone();
        den = den
            * (wire(p, Wire::Wr) + wire(p, Wire::Sigma2) * rp.beta.clone() + rp.gamma.clone())
            * (wire(p, Wire::Wo) + wire(p, Wire::Sigma3) * rp.beta.clone() + rp.gamma.clone())
            * (wire(p, Wire::W4) + wire(p, Wire::Sigma4) * rp.beta.clone() + rp.gamma.clone());
        den
    };

    // Contribution 2
    {
        evals[2] = ((wire(p, Wire::ZPerm) + wire(p, Wire::LagrangeFirst))
            * grand_product_numerator
            - (wire(p, Wire::ZPermShift) + wire(p, Wire::LagrangeLast) * rp.public_inputs_delta.clone())
                * grand_product_denominator)
            * domain_sep.clone();
    }

    // Contribution 3
    {
        evals[3] = wire(p, Wire::LagrangeLast) * wire(p, Wire::ZPermShift) * domain_sep;
    }
}

/// Accumulate the two lookup log-derivative subrelations (indices 4 and 5).
fn accumulate_log_derivative_lookup_relation(
    p: &[Fr],
    rp: &RelationParameters,
    evals: &mut [Fr],
    domain_sep: Fr,
) {
    let write_term = wire(p, Wire::Table1)
        + rp.gamma.clone()
        + wire(p, Wire::Table2) * rp.eta.clone()
        + wire(p, Wire::Table3) * rp.eta_two.clone()
        + wire(p, Wire::Table4) * rp.eta_three.clone();

    let derived_entry_2 = wire(p, Wire::Wr) + wire(p, Wire::Qm) * wire(p, Wire::WrShift);
    let derived_entry_3 = wire(p, Wire::Wo) + wire(p, Wire::Qc) * wire(p, Wire::WoShift);

    let read_term = wire(p, Wire::Wl)
        + rp.gamma.clone()
        + wire(p, Wire::Qr) * wire(p, Wire::WlShift)
        + derived_entry_2 * rp.eta.clone()
        + derived_entry_3 * rp.eta_two.clone()
        + wire(p, Wire::Qo) * rp.eta_three.clone();

    let inv = wire(p, Wire::LookupInverses);
    let inv_exists = wire(p, Wire::LookupReadTags) + wire(p, Wire::QLookup)
        - wire(p, Wire::LookupReadTags) * wire(p, Wire::QLookup);

    evals[4] = (read_term.clone() * write_term.clone() * inv.clone() - inv_exists) * domain_sep.clone();
    evals[5] = wire(p, Wire::QLookup) * (write_term * inv.clone())
        - wire(p, Wire::LookupReadCounts) * (read_term * inv);
}

/// Accumulate the four range-check subrelations (indices 6..9).
fn accumulate_delta_range_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: Fr) {
    let minus_one = Fr::zero(env) - Fr::from_u64(env, 1);
    let minus_two = Fr::zero(env) - Fr::from_u64(env, 2);
    let minus_three = Fr::zero(env) - Fr::from_u64(env, 3);

    let delta_1 = wire(p, Wire::Wr) - wire(p, Wire::Wl);
    let delta_2 = wire(p, Wire::Wo) - wire(p, Wire::Wr);
    let delta_3 = wire(p, Wire::W4) - wire(p, Wire::Wo);
    let delta_4 = wire(p, Wire::WlShift) - wire(p, Wire::W4);
    let deltas = [delta_1, delta_2, delta_3, delta_4];
    let negs = [minus_one, minus_two, minus_three];

    // Contributions 6..9
    for i in 0..4 {
        let mut acc = deltas[i].clone();
        for n in &negs {
            acc = acc * (deltas[i].clone() + n.clone());
        }
        evals[6 + i] = acc * wire(p, Wire::QRange) * domain_sep.clone();
    }
}

/// Accumulate elliptic-curve subrelations (indices 10..11).
fn accumulate_elliptic_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: Fr) {
    let x1 = wire(p, Wire::Wr);
    let y1 = wire(p, Wire::Wo);
    let x2 = wire(p, Wire::WlShift);
    let y2 = wire(p, Wire::W4Shift);
    let x3 = wire(p, Wire::WrShift);
    let y3 = wire(p, Wire::WoShift);

    let q_sign = wire(p, Wire::Ql);
    let q_double = wire(p, Wire::Qm);
    let q_gate = wire(p, Wire::QElliptic);

    let delta_x = x2.clone() - x1.clone();
    let y1_sq = y1.clone() * y1.clone();

    let x_add_id = {
        let y2_sq = y2.clone() * y2.clone();
        let y1y2 = y1.clone() * y2.clone() * q_sign.clone();
        (x3.clone() + x2.clone() + x1.clone()) * delta_x.clone() * delta_x.clone() - y2_sq - y1_sq.clone() + y1y2.clone() + y1y2
    };
    let y_add_id = {
        let y_diff = y2 * q_sign - y1.clone();
        (y1.clone() + y3.clone()) * delta_x + (x3.clone() - x1.clone()) * y_diff
    };

    const B_NEG: u64 = 17;
    let b_neg = Fr::from_u64(env, B_NEG);

    let x_double_id = {
        let x_pow_4 = (y1_sq.clone() + b_neg) * x1.clone();
        let y1_sqr_mul_4 = y1_sq.clone() + y1_sq.clone() + y1_sq.clone() + y1_sq;
        let x_pow_4_mul_9 = x_pow_4 * Fr::from_u64(env, 9);
        (x3.clone() + x1.clone() + x1.clone()) * y1_sqr_mul_4 - x_pow_4_mul_9
    };
    let y_double_id = {
        let x1_sqr_mul_3 = (x1.clone() + x1.clone() + x1.clone()) * x1.clone();
        x1_sqr_mul_3 * (x1 - x3) - (y1.clone() + y1.clone()) * (y1 + y3)
    };

    let add_factor = (Fr::one(env) - q_double.clone()) * q_gate.clone() * domain_sep.clone();
    let double_factor = q_double * q_gate * domain_sep;

    // Contribution 10: elliptic x
    evals[10] = x_add_id * add_factor.clone() + x_double_id * double_factor.clone();
    // Contribution 11: elliptic y
    evals[11] = y_add_id * add_factor + y_double_id * double_factor;
}

/// Accumulate auxiliary subrelations (indices 12..17).
fn accumulate_auxillary_relation(
    env: &Env,
    p: &[Fr],
    rp: &RelationParameters,
    evals: &mut [Fr],
    domain_sep: Fr,
) {
    fn limb_size(env: &Env) -> Fr {
        Fr::from_str(env, "0x100000000000000000")
    }
    fn sublimb_shift(env: &Env) -> Fr {
        Fr::from_u64(env, 1 << 14)
    }

    let ls = limb_size(env);
    let ss = sublimb_shift(env);

    let mut limb_subproduct =
        wire(p, Wire::Wl) * wire(p, Wire::WrShift) + wire(p, Wire::WlShift) * wire(p, Wire::Wr);

    let mut non_native_field_gate_2 = wire(p, Wire::Wl) * wire(p, Wire::W4)
        + wire(p, Wire::Wr) * wire(p, Wire::Wo)
        - wire(p, Wire::WoShift);
    non_native_field_gate_2 =
        non_native_field_gate_2 * ls.clone() - wire(p, Wire::W4Shift) + limb_subproduct.clone();
    non_native_field_gate_2 = non_native_field_gate_2 * wire(p, Wire::Q4);

    limb_subproduct =
        limb_subproduct * ls + wire(p, Wire::WlShift) * wire(p, Wire::WrShift);

    let non_native_field_gate_1 =
        (limb_subproduct.clone() - (wire(p, Wire::Wo) + wire(p, Wire::W4))) * wire(p, Wire::Qo);

    let non_native_field_gate_3 = (limb_subproduct.clone() + wire(p, Wire::W4)
        - (wire(p, Wire::WoShift) + wire(p, Wire::W4Shift)))
        * wire(p, Wire::Qm);

    let non_native_field_identity =
        (non_native_field_gate_1 + non_native_field_gate_2 + non_native_field_gate_3)
            * wire(p, Wire::Qr);

    let mut limb_accumulator_1 = wire(p, Wire::WrShift) * ss.clone() + wire(p, Wire::WlShift);
    limb_accumulator_1 = limb_accumulator_1 * ss.clone() + wire(p, Wire::Wo);
    limb_accumulator_1 = limb_accumulator_1 * ss.clone() + wire(p, Wire::Wr);
    limb_accumulator_1 = limb_accumulator_1 * ss.clone() + wire(p, Wire::Wl);
    limb_accumulator_1 = (limb_accumulator_1 - wire(p, Wire::W4)) * wire(p, Wire::Q4);

    let mut limb_accumulator_2 = wire(p, Wire::WoShift) * ss.clone() + wire(p, Wire::WrShift);
    limb_accumulator_2 = limb_accumulator_2 * ss.clone() + wire(p, Wire::WlShift);
    limb_accumulator_2 = limb_accumulator_2 * ss.clone() + wire(p, Wire::W4);
    limb_accumulator_2 = limb_accumulator_2 * ss + wire(p, Wire::Wo);
    limb_accumulator_2 = (limb_accumulator_2 - wire(p, Wire::W4Shift)) * wire(p, Wire::Qm);

    let limb_accumulator_identity = (limb_accumulator_1 + limb_accumulator_2) * wire(p, Wire::Qo);

    let mut memory_record_check = wire(p, Wire::Wo) * rp.eta_three.clone()
        + wire(p, Wire::Wr) * rp.eta_two.clone()
        + wire(p, Wire::Wl) * rp.eta.clone()
        + wire(p, Wire::Qc);
    let partial_record_check = memory_record_check.clone();
    memory_record_check = memory_record_check - wire(p, Wire::W4);

    let index_delta = wire(p, Wire::WlShift) - wire(p, Wire::Wl);
    let record_delta = wire(p, Wire::W4Shift) - wire(p, Wire::W4);

    let index_is_monotonically_increasing = index_delta.clone() * index_delta.clone() - index_delta.clone();
    let adjacent_values_match_if_adjacent_indices_match = (Fr::one(env) - index_delta.clone()) * record_delta;

    evals[13] = adjacent_values_match_if_adjacent_indices_match
        * wire(p, Wire::Ql)
        * wire(p, Wire::Qr)
        * wire(p, Wire::QAux)
        * domain_sep.clone();
    // Contribution 14: ROM index monotonic
    evals[14] = index_is_monotonically_increasing.clone()
        * wire(p, Wire::Ql)
        * wire(p, Wire::Qr)
        * wire(p, Wire::QAux)
        * domain_sep.clone();

    let access_type = wire(p, Wire::W4) - partial_record_check;
    let access_check = access_type.clone() * access_type.clone() - access_type;

    let mut next_gate_access_type = wire(p, Wire::WoShift) * rp.eta_three.clone()
        + wire(p, Wire::WrShift) * rp.eta_two.clone()
        + wire(p, Wire::WlShift) * rp.eta.clone();
    next_gate_access_type = wire(p, Wire::W4Shift) - next_gate_access_type;

    let value_delta = wire(p, Wire::WoShift) - wire(p, Wire::Wo);
    let adjacent_values_match_if_adjacent_indices_match_and_next_access_is_a_read_operation =
        (Fr::one(env) - index_delta.clone()) * value_delta * (Fr::one(env) - next_gate_access_type.clone());

    // Contribution 15,16,17: RAM
    evals[15] = adjacent_values_match_if_adjacent_indices_match_and_next_access_is_a_read_operation
        * wire(p, Wire::QArith)
        * wire(p, Wire::QAux)
        * domain_sep.clone();
    evals[16] = index_is_monotonically_increasing
        * wire(p, Wire::QArith)
        * wire(p, Wire::QAux)
        * domain_sep.clone();
    evals[17] = (next_gate_access_type.clone() * next_gate_access_type.clone() - next_gate_access_type)
        * wire(p, Wire::QArith)
        * wire(p, Wire::QAux)
        * domain_sep.clone();

    let rom_consistency_check_identity =
        memory_record_check.clone() * wire(p, Wire::Ql) * wire(p, Wire::Qr);
    let ram_timestamp_check_identity = (Fr::one(env) - index_delta)
        * (wire(p, Wire::WrShift) - wire(p, Wire::Wr))
        - wire(p, Wire::Wo);
    let ram_consistency_check_identity = access_check * wire(p, Wire::QArith);

    let memory_identity = rom_consistency_check_identity
        + ram_timestamp_check_identity * wire(p, Wire::Q4) * wire(p, Wire::Ql)
        + memory_record_check * wire(p, Wire::Qm) * wire(p, Wire::Ql)
        + ram_consistency_check_identity;

    let auxiliary_identity =
        memory_identity + non_native_field_identity + limb_accumulator_identity;
    // Contribution 12
    evals[12] = auxiliary_identity * wire(p, Wire::QAux) * domain_sep;
}

/// Accumulate Poseidon external subrelations (indices 18..21).
fn accumulate_poseidon_external_relation(p: &[Fr], evals: &mut [Fr], domain_sep: Fr) {
    let s1 = wire(p, Wire::Wl) + wire(p, Wire::Ql);
    let s2 = wire(p, Wire::Wr) + wire(p, Wire::Qr);
    let s3 = wire(p, Wire::Wo) + wire(p, Wire::Qo);
    let s4 = wire(p, Wire::W4) + wire(p, Wire::Q4);

    let u1_ext = s1.pow(5);
    let u2_ext = s2.pow(5);
    let u3_ext = s3.pow(5);
    let u4_ext = s4.pow(5);

    let t0 = u1_ext.clone() + u2_ext.clone();
    let t1 = u3_ext.clone() + u4_ext.clone();
    let t2 = u2_ext.clone() + u2_ext + t1.clone();
    let t3 = u4_ext.clone() + u4_ext + t0.clone();

    let v4 = t1.clone() + t1.clone() + t1.clone() + t1 + t3.clone();
    let v2 = t0.clone() + t0.clone() + t0.clone() + t0 + t2.clone();
    let v1 = t3 + v2.clone();
    let v3 = t2 + v4.clone();

    let q_poseidon = wire(p, Wire::QPoseidon2External);
    evals[18] = (v1 - wire(p, Wire::WlShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[19] = (v2 - wire(p, Wire::WrShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[20] = (v3 - wire(p, Wire::WoShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[21] = (v4 - wire(p, Wire::W4Shift)) * q_poseidon * domain_sep;
}

/// Accumulate Poseidon internal subrelations (indices 22..25).
fn accumulate_poseidon_internal_relation(env: &Env, p: &[Fr], evals: &mut [Fr], domain_sep: Fr) {
    let u1_int = (wire(p, Wire::Wl) + wire(p, Wire::Ql)).pow(5);
    let u2_int = wire(p, Wire::Wr);
    let u3_int = wire(p, Wire::Wo);
    let u4_int = wire(p, Wire::W4);
    let q_poseidon = wire(p, Wire::QPoseidon2Internal);
    let u_sum = u1_int.clone() + u2_int.clone() + u3_int.clone() + u4_int.clone();
    let diag = internal_matrix_diagonal(env);

    let w1 = u1_int * diag[0].clone() + u_sum.clone();
    let w2 = u2_int * diag[1].clone() + u_sum.clone();
    let w3 = u3_int * diag[2].clone() + u_sum.clone();
    let w4 = u4_int * diag[3].clone() + u_sum;

    evals[22] = (w1 - wire(p, Wire::WlShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[23] = (w2 - wire(p, Wire::WrShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[24] = (w3 - wire(p, Wire::WoShift)) * q_poseidon.clone() * domain_sep.clone();
    evals[25] = (w4 - wire(p, Wire::W4Shift)) * q_poseidon * domain_sep;
}

/// Batch all NUM_SUBRELATIONS = 26 subrelations with the alpha challenges.
fn scale_and_batch_subrelations(evaluations: &[Fr], subrelation_challenges: &[Fr]) -> Fr {
    let mut accumulator = evaluations[0].clone();
    for i in 1..NUMBER_OF_SUBRELATIONS {
        accumulator = accumulator + evaluations[i].clone() * subrelation_challenges[i - 1].clone();
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

    accumulate_arithmetic_relation(env, purported_evaluations, &mut evaluations, pow_partial_eval.clone());
    accumulate_permutation_relation(
        purported_evaluations,
        rp,
        &mut evaluations,
        pow_partial_eval.clone(),
    );
    accumulate_log_derivative_lookup_relation(
        purported_evaluations,
        rp,
        &mut evaluations,
        pow_partial_eval.clone(),
    );
    accumulate_delta_range_relation(env, purported_evaluations, &mut evaluations, pow_partial_eval.clone());
    accumulate_elliptic_relation(env, purported_evaluations, &mut evaluations, pow_partial_eval.clone());
    accumulate_auxillary_relation(
        env,
        purported_evaluations,
        rp,
        &mut evaluations,
        pow_partial_eval.clone(),
    );
    accumulate_poseidon_external_relation(
        purported_evaluations,
        &mut evaluations,
        pow_partial_eval.clone(),
    );
    accumulate_poseidon_internal_relation(
        env,
        purported_evaluations,
        &mut evaluations,
        pow_partial_eval,
    );

    let accumulator = scale_and_batch_subrelations(&evaluations, alphas);
    accumulator
}
