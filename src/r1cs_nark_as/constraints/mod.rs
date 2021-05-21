use crate::constraints::ASVerifierGadget;
use crate::hp_as::constraints::ASForHPVerifierGadget;
use crate::hp_as::constraints::{
    InputInstanceVar as HPInputInstanceVar, VerifierKeyVar as HPVerifierKeyVar,
};
use crate::r1cs_nark_as::{
    r1cs_nark, ASForR1CSNark, InputInstance, CHALLENGE_SIZE, HP_AS_PROTOCOL_NAME, PROTOCOL_NAME,
};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::vec;
use ark_std::vec::Vec;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
pub struct ASForR1CSNarkVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    _affine: PhantomData<G>,
    _curve: PhantomData<C>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> ASForR1CSNarkVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    /// Check that the input instance is properly structured.
    fn check_input_instance_structure(
        input_instance: &InputInstanceVar<G, C>,
        r1cs_input_len: usize,
    ) -> bool {
        // The lengths of the R1CS inputs and witnesses to be accumulated must be supported by the
        // index key.
        return input_instance.r1cs_input.len() == r1cs_input_len;
    }

    /// Check that the accumulator instance is properly structured.
    fn check_accumulator_instance_structure(
        accumulator_instance: &AccumulatorInstanceVar<G, C>,
        r1cs_input_len: usize,
    ) -> bool {
        // The length of the R1CS input must be equal to those of the other R1CS inputs being
        // accumulated.
        return accumulator_instance.r1cs_input.len() == r1cs_input_len;
    }

    /// Computes the linear combination of commitments.
    #[tracing::instrument(target = "r1cs", skip(commitments, challenges))]
    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a C>,
        challenges: &[Vec<Boolean<ConstraintF<G>>>],
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = C::zero();
        for (commitment, challenge) in commitments.into_iter().zip(challenges) {
            if challenge.len() == 1 && challenge[0].eq(&Boolean::TRUE) {
                combined_commitment += commitment
            } else {
                combined_commitment += &commitment.scalar_mul_le(challenge.iter())?
            }
        }

        Ok(combined_commitment)
    }

    /// Computes the gamma challenges using the provided sponge.
    #[tracing::instrument(target = "r1cs", skip(input, msg, nark_sponge))]
    fn compute_gamma_challenge(
        input: &[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>],
        msg: &FirstRoundMessageVar<G, C>,
        mut nark_sponge: impl CryptographicSpongeVar<ConstraintF<G>, S>,
    ) -> Result<
        (
            NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
            Vec<Boolean<ConstraintF<G>>>,
        ),
        SynthesisError,
    > {
        let mut input_bytes = Vec::new();
        for elem in input {
            input_bytes.append(&mut elem.to_bytes()?);
        }

        absorb_gadget!(&mut nark_sponge, input_bytes, msg);

        let mut squeezed = nark_sponge.squeeze_nonnative_field_elements_with_sizes(&[
            FieldElementSize::Truncated(CHALLENGE_SIZE),
        ])?;

        Ok((squeezed.0.pop().unwrap(), squeezed.1.pop().unwrap()))
    }

    /// Computes the beta challenges using the provided sponge.
    #[tracing::instrument(
        target = "r1cs",
        skip(
            num_challenges,
            as_matrices_hash,
            accumulator_instances,
            input_instances,
            proof_randomness,
            as_sponge,
        )
    )]
    fn compute_beta_challenges(
        num_challenges: usize,
        as_matrices_hash: &Vec<FpVar<ConstraintF<G>>>,
        accumulator_instances: &Vec<&AccumulatorInstanceVar<G, C>>,
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        proof_randomness: Option<&ProofRandomnessVar<G, C>>,
        mut as_sponge: impl CryptographicSpongeVar<ConstraintF<G>, S>,
    ) -> Result<
        (
            Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,
            Vec<Vec<Boolean<ConstraintF<G>>>>,
        ),
        SynthesisError,
    > {
        absorb_gadget!(
            &mut as_sponge,
            as_matrices_hash,
            accumulator_instances,
            input_instances,
            proof_randomness
        );

        let mut squeeze = as_sponge.squeeze_nonnative_field_elements_with_sizes(
            vec![FieldElementSize::Truncated(CHALLENGE_SIZE); num_challenges - 1].as_slice(),
        )?;

        let mut outputs_fe = Vec::with_capacity(num_challenges);
        let mut outputs_bits = Vec::with_capacity(num_challenges);

        outputs_fe.push(NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::one());
        outputs_bits.push(vec![Boolean::TRUE]);

        outputs_fe.append(&mut squeeze.0);
        outputs_bits.append(&mut squeeze.1);

        Ok((outputs_fe, outputs_bits))
    }

    /// Blinds the commitments from the first round messages.
    #[tracing::instrument(target = "r1cs", skip(index_info, input_instances, nark_sponge))]
    fn compute_blinded_commitments(
        index_info: &IndexInfoVar<ConstraintF<G>>,
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        mut nark_sponge: impl CryptographicSpongeVar<ConstraintF<G>, S>,
    ) -> Result<(Vec<C>, Vec<C>, Vec<C>, Vec<C>), SynthesisError> {
        let mut all_blinded_comm_a = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_b = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_c = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_prod = Vec::with_capacity(input_instances.len());

        nark_sponge.absorb(&index_info.matrices_hash)?;

        for instance in input_instances {
            let first_round_message: &FirstRoundMessageVar<G, C> = &instance.first_round_message;

            let mut comm_a = first_round_message.comm_a.clone();
            let mut comm_b = first_round_message.comm_b.clone();
            let mut comm_c = first_round_message.comm_c.clone();
            let mut comm_prod = first_round_message.comm_c.clone();

            if let Some(first_msg_randomness) = first_round_message.randomness.as_ref() {
                let (mut gamma_challenge_fe, gamma_challenge_bits) = Self::compute_gamma_challenge(
                    &instance.r1cs_input.as_slice(),
                    &instance.first_round_message,
                    nark_sponge.clone(),
                )?;

                comm_a += &first_msg_randomness
                    .comm_r_a
                    .scalar_mul_le(gamma_challenge_bits.iter())?;

                comm_b += &first_msg_randomness
                    .comm_r_b
                    .scalar_mul_le(gamma_challenge_bits.iter())?;

                comm_c += &first_msg_randomness
                    .comm_r_c
                    .scalar_mul_le(gamma_challenge_bits.iter())?;

                comm_prod += &(first_msg_randomness
                    .comm_1
                    .scalar_mul_le(gamma_challenge_bits.iter())?
                    + &first_msg_randomness.comm_2.scalar_mul_le(
                        gamma_challenge_fe.square_in_place()?.to_bits_le()?.iter(),
                    )?);
            }

            all_blinded_comm_a.push(comm_a);
            all_blinded_comm_b.push(comm_b);
            all_blinded_comm_c.push(comm_c);
            all_blinded_comm_prod.push(comm_prod);
        }

        Ok((
            all_blinded_comm_a,
            all_blinded_comm_b,
            all_blinded_comm_c,
            all_blinded_comm_prod,
        ))
    }

    /// Compute the input instances for HP_AS using the blinded commitments.
    #[tracing::instrument(
        target = "r1cs",
        skip(all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_prod)
    )]
    fn compute_hp_input_instances(
        all_blinded_comm_a: &Vec<C>,
        all_blinded_comm_b: &Vec<C>,
        all_blinded_comm_prod: &Vec<C>,
    ) -> Vec<HPInputInstanceVar<G, C>> {
        assert!(
            all_blinded_comm_a.len() == all_blinded_comm_b.len()
                && all_blinded_comm_b.len() == all_blinded_comm_prod.len()
        );

        let mut input_instances = Vec::with_capacity(all_blinded_comm_a.len());
        all_blinded_comm_a
            .into_iter()
            .zip(all_blinded_comm_b)
            .zip(all_blinded_comm_prod)
            .for_each(|((comm_a, comm_b), comm_prod)| {
                input_instances.push(HPInputInstanceVar {
                    comm_1: comm_a.clone(),
                    comm_2: comm_b.clone(),
                    comm_3: comm_prod.clone(),
                    _curve: PhantomData,
                });
            });

        input_instances
    }

    /// Computes the linear combination of vectors.
    #[tracing::instrument(target = "r1cs", skip(vectors, challenges))]
    fn combine_vectors<'a>(
        vectors: impl IntoIterator<Item = &'a Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>>,
        challenges: &[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>],
    ) -> Result<Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>, SynthesisError> {
        let mut output = Vec::new();
        for (ni, vector) in vectors.into_iter().enumerate() {
            for (li, elem) in vector.into_iter().enumerate() {
                let product = elem.mul_without_reduce(&challenges[ni])?;
                if li >= output.len() {
                    output.push(product);
                } else {
                    output[li] += &product;
                }
            }
        }

        let mut reduced_output = Vec::with_capacity(output.len());
        for mul_result in output {
            reduced_output.push(mul_result.reduce()?);
        }

        Ok(reduced_output)
    }

    /// Computes a part of a new accumulator instance. Does not compute the HP_AS input instance, so
    /// an accumulator instance is not yet fully constructed.
    #[tracing::instrument(
        target = "r1cs",
        skip(
            input_instances,
            all_blinded_comm_a,
            all_blinded_comm_b,
            all_blinded_comm_c,
            accumulator_instances,
            beta_challenges_fe,
            beta_challenges_bits,
            proof_randomness
        )
    )]
    fn compute_accumulator_instance_components(
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        all_blinded_comm_a: &Vec<C>,
        all_blinded_comm_b: &Vec<C>,
        all_blinded_comm_c: &Vec<C>,
        accumulator_instances: &Vec<&AccumulatorInstanceVar<G, C>>,
        beta_challenges_fe: &Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,
        beta_challenges_bits: &Vec<Vec<Boolean<ConstraintF<G>>>>,
        proof_randomness: Option<&ProofRandomnessVar<G, C>>,
    ) -> Result<
        (
            Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>, // Combined R1CS input
            C,                                                      // Combined comm_a
            C,                                                      // Combined comm_b
            C,                                                      // Combined comm_c
        ),
        SynthesisError,
    > {
        assert!(
            input_instances.len() == all_blinded_comm_a.len()
                && all_blinded_comm_a.len() == all_blinded_comm_b.len()
                && all_blinded_comm_b.len() == all_blinded_comm_c.len()
        );

        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if proof_randomness.is_some() { 1 } else { 0 };

        assert!(num_addends <= beta_challenges_fe.len());
        assert_eq!(beta_challenges_fe.len(), beta_challenges_bits.len());

        let r1cs_inputs = accumulator_instances
            .iter()
            .map(|instance| &instance.r1cs_input)
            .chain(input_instances.iter().map(|instance| &instance.r1cs_input));

        let all_comm_a = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_a)
            .chain(all_blinded_comm_a);

        let all_comm_b = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_b)
            .chain(all_blinded_comm_b);

        let all_comm_c = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_c)
            .chain(all_blinded_comm_c);

        let (r1cs_inputs, all_comm_a, all_comm_b, all_comm_c) = if proof_randomness.is_some() {
            (
                r1cs_inputs.chain(vec![&proof_randomness.as_ref().unwrap().r1cs_r_input]),
                all_comm_a.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_a]),
                all_comm_b.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_b]),
                all_comm_c.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_c]),
            )
        } else {
            (
                r1cs_inputs.chain(vec![]),
                all_comm_a.chain(vec![]),
                all_comm_b.chain(vec![]),
                all_comm_c.chain(vec![]),
            )
        };

        let combined_r1cs_input =
            Self::combine_vectors(r1cs_inputs, beta_challenges_fe.as_slice())?;

        let combined_comm_a =
            Self::combine_commitments(all_comm_a, beta_challenges_bits.as_slice())?;

        let combined_comm_b =
            Self::combine_commitments(all_comm_b, beta_challenges_bits.as_slice())?;

        let combined_comm_c =
            Self::combine_commitments(all_comm_c, beta_challenges_bits.as_slice())?;

        Ok((
            combined_r1cs_input,
            combined_comm_a,
            combined_comm_b,
            combined_comm_c,
        ))
    }
}

impl<G, C, CS, S, SV> ASVerifierGadget<ConstraintF<G>, S, SV, ASForR1CSNark<G, CS, S>>
    for ASForR1CSNarkVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    type VerifierKey = VerifierKeyVar<ConstraintF<G>>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = AccumulatorInstanceVar<G, C>;
    type Proof = ProofVar<G, C>;

    #[tracing::instrument(
        target = "r1cs",
        skip(
            verifier_key,
            input_instances,
            old_accumulator_instances,
            new_accumulator_instance,
            proof,
            sponge,
        )
    )]
    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<SV>,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| SV::new(cs.clone()));

        let nark_sponge = sponge.fork(r1cs_nark::PROTOCOL_NAME)?;
        let as_sponge = sponge.fork(PROTOCOL_NAME)?;
        let hp_sponge = sponge.fork(HP_AS_PROTOCOL_NAME)?;

        let make_zk_enabled = proof.randomness.is_some();
        let r1cs_input_len = verifier_key.nark_index.num_instance_variables;

        let mut input_instances = input_instances.into_iter().collect::<Vec<_>>();
        for instance in &input_instances {
            if !Self::check_input_instance_structure(instance, r1cs_input_len) {
                return Ok(Boolean::FALSE);
            }
        }

        let old_accumulator_instances = old_accumulator_instances.into_iter().collect::<Vec<_>>();
        for instance in &old_accumulator_instances {
            if !Self::check_accumulator_instance_structure(instance, r1cs_input_len) {
                return Ok(Boolean::FALSE);
            }
        }

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if input_instances.is_empty() && old_accumulator_instances.is_empty() {
            default_input_instance = Some(InputInstanceVar::new_constant(
                sponge.cs(),
                InputInstance::zero(r1cs_input_len, false),
            )?);
            input_instances.push(default_input_instance.as_ref().unwrap());
        }

        // Step 1 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let num_addends = input_instances.len()
            + old_accumulator_instances.len()
            + if make_zk_enabled { 1 } else { 0 };

        let (beta_challenges_fe, beta_challenges_bits) = Self::compute_beta_challenges(
            num_addends,
            &verifier_key.as_matrices_hash,
            &old_accumulator_instances,
            &input_instances,
            proof.randomness.as_ref(),
            as_sponge,
        )?;

        // Step 2 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                &verifier_key.nark_index,
                &input_instances,
                nark_sponge,
            )?;

        let hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let hp_accumulator_instances = old_accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        // Step 4 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let hp_vk = HPVerifierKeyVar::<ConstraintF<G>>::new_constant(
            cs.clone(),
            verifier_key.nark_index.num_constraints,
        )?;

        let hp_verify = ASForHPVerifierGadget::<G, C, S, SV>::verify(
            cs,
            &hp_vk,
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
            Some(hp_sponge),
        )?;

        // Steps 5-6 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &old_accumulator_instances,
            &beta_challenges_fe,
            &beta_challenges_bits,
            proof.randomness.as_ref(),
        )?;

        let mut verify_result = hp_verify;

        if r1cs_input.len() != new_accumulator_instance.r1cs_input.len() {
            return Ok(Boolean::FALSE);
        }

        for (input, claimed_input) in r1cs_input.iter().zip(&new_accumulator_instance.r1cs_input) {
            verify_result = verify_result.and(&input.is_eq(claimed_input)?)?;
        }

        verify_result = verify_result.and(&comm_a.is_eq(&new_accumulator_instance.comm_a)?)?;
        verify_result = verify_result.and(&comm_b.is_eq(&new_accumulator_instance.comm_b)?)?;
        verify_result = verify_result.and(&comm_c.is_eq(&new_accumulator_instance.comm_c)?)?;

        Ok(verify_result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::tests::ASVerifierGadgetTests;
    use crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget;
    use crate::r1cs_nark_as::tests::{
        ASForR1CSNarkTestInput, ASForR1CSNarkTestParams, DummyCircuit,
    };
    use crate::r1cs_nark_as::ASForR1CSNark;
    use ark_relations::r1cs::SynthesisError;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = ASForR1CSNark<G, DummyCircuit<F>, Sponge>;
    type I = ASForR1CSNarkTestInput<CF, Sponge>;
    type ASV = ASForR1CSNarkVerifierGadget<G, C, Sponge, SpongeVar>;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn single_input_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }
}
