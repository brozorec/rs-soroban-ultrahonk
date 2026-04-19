//! Shplemini batch-opening verifier for BN254
use crate::ec::{g1_msm, g1_negate, pairing_check};
use crate::field::{batch_inverse, Fr};
use crate::trace;
use crate::types::{
    G1Point, Proof, Transcript, VerificationKey, CONST_PROOF_SIZE_LOG_N, NUMBER_OF_ENTITIES,
    NUMBER_TO_BE_SHIFTED, NUMBER_UNSHIFTED,
};
use soroban_sdk::Env;

/// Shplemini verification
pub fn verify_shplemini(
    env: &Env,
    proof: &Proof,
    vk: &VerificationKey,
    tp: &Transcript,
) -> Result<(), &'static str> {
    // 1) r^{2^i}
    let log_n = vk.log_circuit_size as usize;
    let mut r_pows: [Fr; CONST_PROOF_SIZE_LOG_N] =
        core::array::from_fn(|_| Fr::zero(env));
    r_pows[0] = tp.gemini_r.clone();
    for i in 1..log_n {
        r_pows[i] = r_pows[i - 1].clone() * r_pows[i - 1].clone();
    }

    // We need the following inversions:
    //   - (z - r^0), (z + r^0)          for shplonk weights (pos0, neg0)
    //   - gemini_r                       for shifted weight
    //   - (r^j*(1-u_j) + u_j)           for j in 1..=log_n  (fold round denoms)
    //   - (z - r^j), (z + r^j)          for j in 1..log_n   (further folding)
    //
    // Total: 2 + 1 + log_n + 2*(log_n - 1) = 3*log_n + 1 values.

    // Collect all values to invert into a flat array.
    const MAX_BATCH: usize = 3 * CONST_PROOF_SIZE_LOG_N + 1;
    let batch_size = 3 + log_n + 2 * (log_n - 1);
    let mut to_invert: [Fr; MAX_BATCH] =
        core::array::from_fn(|_| Fr::zero(env));
    let mut inverted: [Fr; MAX_BATCH] =
        core::array::from_fn(|_| Fr::zero(env));

    to_invert[0] = tp.shplonk_z.clone() - r_pows[0].clone();
    to_invert[1] = tp.shplonk_z.clone() + r_pows[0].clone();
    to_invert[2] = tp.gemini_r.clone();

    // fold round denominators: r^j * (1 - u_j) + u_j, for j = log_n down to 1
    for j in (1..=log_n).rev() {
        let u = tp.sumcheck_u_challenges[j - 1].clone();
        to_invert[3 + (log_n - j)] = r_pows[j - 1].clone() * (Fr::one(env) - u.clone()) + u;
    }

    // further folding denominators: (z - r^j) and (z + r^j) for j = 1..log_n
    let further_base = 3 + log_n;
    for j in 1..log_n {
        to_invert[further_base + 2 * (j - 1)] = tp.shplonk_z.clone() - r_pows[j].clone();
        to_invert[further_base + 2 * (j - 1) + 1] = tp.shplonk_z.clone() + r_pows[j].clone();
    }

    batch_inverse(&to_invert[..batch_size], &mut inverted[..batch_size]).map_err(|_| {
        "shplemini: batch inversion failed (zero denominator in shplonk/gemini/fold)"
    })?;

    // Unpack results
    let pos0 = inverted[0].clone();
    let neg0 = inverted[1].clone();
    let gemini_r_inv = inverted[2].clone();

    // 2) allocate arrays
    const TOTAL: usize = 1 + NUMBER_OF_ENTITIES + CONST_PROOF_SIZE_LOG_N + 1;
    trace!("total = {}", TOTAL);
    let mut scalars: [Fr; TOTAL] =
        core::array::from_fn(|_| Fr::zero(env));
    let mut coms = [G1Point::infinity(); TOTAL];

    // 3) compute shplonk weights
    let unshifted = pos0.clone() + tp.shplonk_nu.clone() * neg0.clone();
    let shifted = gemini_r_inv * (pos0.clone() - tp.shplonk_nu.clone() * neg0.clone());
    // 4) shplonk_Q
    scalars[0] = Fr::one(env);
    coms[0] = proof.shplonk_q.clone();

    // 5) weight sumcheck evals
    let mut rho_pow = Fr::one(env);
    let mut eval_acc = Fr::zero(env);
    let shifted_end = NUMBER_UNSHIFTED + NUMBER_TO_BE_SHIFTED;
    debug_assert_eq!(NUMBER_OF_ENTITIES, shifted_end);
    for (idx, eval) in proof
        .sumcheck_evaluations
        .iter()
        .take(NUMBER_OF_ENTITIES)
        .enumerate()
    {
        let scalar = if idx < NUMBER_UNSHIFTED {
            -unshifted.clone()
        } else {
            -shifted.clone()
        } * rho_pow.clone();
        scalars[1 + idx] = scalar;
        eval_acc = eval_acc + (eval.clone() * rho_pow.clone());
        rho_pow = rho_pow * tp.rho.clone();
    }
    // 6) load VK & proof
    {
        let mut j = 1;
        macro_rules! push {
            ($f:ident) => {{
                coms[j] = vk.$f.clone();
                j += 1;
            }};
        }
        push!(qm);
        push!(qc);
        push!(ql);
        push!(qr);
        push!(qo);
        push!(q4);
        push!(q_lookup);
        push!(q_arith);
        push!(q_delta_range);
        push!(q_elliptic);
        push!(q_aux);
        push!(q_poseidon2_external);
        push!(q_poseidon2_internal);
        push!(s1);
        push!(s2);
        push!(s3);
        push!(s4);
        push!(id1);
        push!(id2);
        push!(id3);
        push!(id4);
        push!(t1);
        push!(t2);
        push!(t3);
        push!(t4);
        push!(lagrange_first);
        push!(lagrange_last);

        coms[j] = proof.w1.clone();
        j += 1;
        coms[j] = proof.w2.clone();
        j += 1;
        coms[j] = proof.w3.clone();
        j += 1;
        coms[j] = proof.w4.clone();
        j += 1;
        coms[j] = proof.z_perm.clone();
        j += 1;
        coms[j] = proof.lookup_inverses.clone();
        j += 1;
        coms[j] = proof.lookup_read_counts.clone();
        j += 1;
        coms[j] = proof.lookup_read_tags.clone();
        j += 1;

        coms[j] = proof.w1.clone();
        j += 1;
        coms[j] = proof.w2.clone();
        j += 1;
        coms[j] = proof.w3.clone();
        j += 1;
        coms[j] = proof.w4.clone();
        j += 1;
        coms[j] = proof.z_perm.clone();
        j += 1;
        let _ = j;
    }

    // 7) folding rounds — use batch-inverted denominators
    let mut fold_pos: [Fr; CONST_PROOF_SIZE_LOG_N] =
        core::array::from_fn(|_| Fr::zero(env));
    let mut cur = eval_acc;
    for j in (1..=log_n).rev() {
        let r2 = r_pows[j - 1].clone();
        let u = tp.sumcheck_u_challenges[j - 1].clone();
        let num = r2.clone() * cur.clone() * Fr::from_u64(env, 2)
            - proof.gemini_a_evaluations[j - 1].clone() * (r2 * (Fr::one(env) - u.clone()) - u);
        let den_inv = inverted[3 + (log_n - j)].clone();
        cur = num * den_inv;
        fold_pos[j - 1] = cur.clone();
    }
    // 8) accumulate constant term
    let mut const_acc = fold_pos[0].clone() * pos0 + proof.gemini_a_evaluations[0].clone() * tp.shplonk_nu.clone() * neg0;
    let mut v_pow = tp.shplonk_nu.clone() * tp.shplonk_nu.clone();
    // 9) further folding + commit — use batch-inverted denominators
    let base = 1 + NUMBER_OF_ENTITIES;
    for j in 1..log_n {
        let pos_inv = inverted[further_base + 2 * (j - 1)].clone();
        let neg_inv = inverted[further_base + 2 * (j - 1) + 1].clone();
        let sp = v_pow.clone() * pos_inv;
        let sn = v_pow.clone() * tp.shplonk_nu.clone() * neg_inv;

        scalars[base + j - 1] = -(sp.clone() + sn.clone());
        const_acc = const_acc + proof.gemini_a_evaluations[j].clone() * sn + fold_pos[j].clone() * sp;

        v_pow = v_pow * tp.shplonk_nu.clone() * tp.shplonk_nu.clone();

        coms[base + j - 1] = proof.gemini_fold_comms[j - 1].clone();
    }

    // Fill remaining (dummy) fold commitments so MSM layout matches Solidity (total 27 entries)
    for i in (log_n - 1)..(CONST_PROOF_SIZE_LOG_N - 1) {
        coms[base + i] = proof.gemini_fold_comms[i].clone();
    }

    // 10) add generator
    let one_idx = base + (CONST_PROOF_SIZE_LOG_N - 1);
    trace!("one_idx = {}", one_idx);
    coms[one_idx] = G1Point::generator();
    scalars[one_idx] = const_acc;

    // 11) add quotient
    let q_idx = one_idx + 1;
    trace!("q_idx = {}", q_idx);
    coms[q_idx] = proof.kzg_quotient.clone();
    scalars[q_idx] = tp.shplonk_z.clone();

    // 12) MSM + pairing
    let p0 = g1_msm(env, &coms, &scalars)?;
    let p1 = g1_negate(env, &proof.kzg_quotient);
    if pairing_check(env, &p0, &p1) {
        Ok(())
    } else {
        Err("Shplonk pairing check failed")
    }
}
