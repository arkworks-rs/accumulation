use crate::constraints::{ASVerifierGadget, ConstraintF, NNFieldVar};
use crate::hp_as::constraints::data_structures::{
    InputInstanceVar as HPInputInstanceVar, VerifierKeyVar as HPVerifierKeyVar,
};
use crate::hp_as::constraints::HpASVerifierGadget;
use crate::nark_as::data_structures::{SimpleNARKDomain, SimpleNARKVerifierASDomain};
use crate::nark_as::NarkAS;
use ark_ec::AffineCurve;
use ark_ff::One;
use ark_ff::ToConstraintField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{CryptographicSpongeVar, DomainSeparatedSpongeVar};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use data_structures::*;
use std::marker::PhantomData;

pub mod data_structures;

pub struct NarkASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    _affine: PhantomData<G>,
    _curve: PhantomData<C>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> NarkASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
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

    fn compute_gamma_challenge(
        sponge: &mut DomainSeparatedSpongeVar<ConstraintF<G>, S, SV, SimpleNARKDomain>,
        input: &[NNFieldVar<G>],
        msg: &FirstRoundMessageVar<G, C>,
    ) -> Result<(NNFieldVar<G>, Vec<Boolean<ConstraintF<G>>>), SynthesisError> {
        let mut input_bytes = Vec::new();
        for elem in input {
            input_bytes.append(&mut elem.to_bytes()?);
        }
        sponge.absorb(input_bytes.to_constraint_field()?.as_slice())?;
        msg.absorb_into_sponge(sponge);

        let mut squeezed =
            sponge.squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 128,
            }])?;

        Ok((squeezed.0.pop().unwrap(), squeezed.1.pop().unwrap()))
    }

    fn compute_beta_challenges(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        num_challenges: usize,
        as_matrices_hash: &Vec<FpVar<ConstraintF<G>>>,
        accumulator_instances: &Vec<&AccumulatorInstanceVar<G, C>>,
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        proof_randomness: Option<&ProofRandomnessVar<G, C>>,
    ) -> Result<(Vec<NNFieldVar<G>>, Vec<Vec<Boolean<ConstraintF<G>>>>), SynthesisError> {
        let mut sponge =
            DomainSeparatedSpongeVar::<ConstraintF<G>, S, SV, SimpleNARKVerifierASDomain>::new(
                cs.clone(),
            );

        sponge.absorb(as_matrices_hash.as_ref())?;

        for acc_instance in accumulator_instances {
            acc_instance.absorb_into_sponge(&mut sponge)?;
        }

        for input_instance in input_instances {
            input_instance.absorb_into_sponge(&mut sponge)?;
        }

        sponge.absorb(&[FpVar::from(Boolean::Constant(proof_randomness.is_some()))])?;
        if let Some(proof_randomness) = proof_randomness {
            proof_randomness.absorb_into_sponge(&mut sponge)?;
        };

        let mut squeeze = sponge.squeeze_nonnative_field_elements_with_sizes(
            vec![FieldElementSize::Truncated { num_bits: 128 }; num_challenges - 1].as_slice(),
        )?;

        let mut outputs_fe = Vec::with_capacity(num_challenges);
        let mut outputs_bits = Vec::with_capacity(num_challenges);

        outputs_fe.push(NNFieldVar::<G>::one());
        outputs_bits.push(vec![Boolean::TRUE]);

        outputs_fe.append(&mut squeeze.0);
        outputs_bits.append(&mut squeeze.1);

        Ok((outputs_fe, outputs_bits))
    }

    fn compute_blinded_commitments(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        index_info: &IndexInfoVar<ConstraintF<G>>,
        input_instances: &Vec<&InputInstanceVar<G, C>>,
    ) -> Result<(Vec<C>, Vec<C>, Vec<C>, Vec<C>), SynthesisError> {
        let mut all_blinded_comm_a = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_b = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_c = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_prod = Vec::with_capacity(input_instances.len());

        let mut sponge =
            DomainSeparatedSpongeVar::<ConstraintF<G>, S, SV, SimpleNARKDomain>::new(cs.clone());
        sponge.absorb(&index_info.matrices_hash.as_ref());

        for instance in input_instances {
            let first_round_message: &FirstRoundMessageVar<G, C> = &instance.first_round_message;

            let mut comm_a = first_round_message.comm_a.clone();
            let mut comm_b = first_round_message.comm_b.clone();
            let mut comm_c = first_round_message.comm_c.clone();
            let mut comm_prod = first_round_message.comm_c.clone();

            if instance.make_zk {
                let mut gamma_sponge = sponge.clone();
                let (mut gamma_challenge_fe, gamma_challenge_bits) = Self::compute_gamma_challenge(
                    &mut gamma_sponge,
                    &instance.r1cs_input.as_slice(),
                    &instance.first_round_message,
                )?;

                if let Some(comm_r_a) = first_round_message.comm_r_a.as_ref() {
                    comm_a += &comm_r_a.scalar_mul_le(gamma_challenge_bits.iter())?;
                }

                if let Some(comm_r_b) = first_round_message.comm_r_b.as_ref() {
                    comm_b += &comm_r_b.scalar_mul_le(gamma_challenge_bits.iter())?;
                }

                if let Some(comm_r_c) = first_round_message.comm_r_c.as_ref() {
                    comm_c += &comm_r_c.scalar_mul_le(gamma_challenge_bits.iter())?;
                }

                if let Some(comm_1) = first_round_message.comm_1.as_ref() {
                    comm_prod += &comm_1.scalar_mul_le(gamma_challenge_bits.iter())?;
                }

                if let Some(comm_2) = first_round_message.comm_2.as_ref() {
                    comm_prod += &comm_2.scalar_mul_le(
                        gamma_challenge_fe.square_in_place()?.to_bits_le()?.iter(),
                    )?;
                }
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

    fn combine_vectors<'a>(
        vectors: impl IntoIterator<Item = &'a Vec<NNFieldVar<G>>>,
        challenges: &[NNFieldVar<G>],
    ) -> Result<Vec<NNFieldVar<G>>, SynthesisError> {
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

    fn compute_accumulator_instance_components(
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        all_blinded_comm_a: &Vec<C>,
        all_blinded_comm_b: &Vec<C>,
        all_blinded_comm_c: &Vec<C>,
        accumulator_instances: &Vec<&AccumulatorInstanceVar<G, C>>,
        beta_challenges_fe: &Vec<NNFieldVar<G>>,
        beta_challenges_bits: &Vec<Vec<Boolean<ConstraintF<G>>>>,
        proof_randomness: Option<&ProofRandomnessVar<G, C>>,
    ) -> Result<(Vec<NNFieldVar<G>>, C, C, C), SynthesisError> {
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

impl<G, C, CS, S, SV> ASVerifierGadget<NarkAS<G, CS, S>, ConstraintF<G>>
    for NarkASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    type VerifierKey = VerifierKeyVar<ConstraintF<G>>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = AccumulatorInstanceVar<G, C>;
    type Proof = ProofVar<G, C>;

    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        let input_instances = input_instances.into_iter().collect::<Vec<_>>();
        let accumulator_instances = accumulator_instances.into_iter().collect::<Vec<_>>();

        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if proof.randomness.is_some() { 1 } else { 0 };

        let (beta_challenges_fe, beta_challenges_bits) = Self::compute_beta_challenges(
            cs.clone(),
            num_addends,
            &verifier_key.as_matrices_hash,
            &accumulator_instances,
            &input_instances,
            proof.randomness.as_ref(),
        )?;

        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                cs.clone(),
                &verifier_key.nark_index,
                &input_instances,
            )?;

        let hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        let hp_accumulator_instances = accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        let hp_vk = HPVerifierKeyVar::<ConstraintF<G>>::new_constant(
            cs.clone(),
            verifier_key.nark_index.num_constraints,
        )?;

        let hp_verify = HpASVerifierGadget::<G, C, S, SV>::verify(
            cs.clone(),
            &hp_vk,
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
        )?;

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &accumulator_instances,
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
    use crate::nark_as::constraints::NarkASVerifierGadget;
    use crate::nark_as::tests::{DummyCircuit, NarkASTestInput, NarkASTestParams};
    use crate::nark_as::NarkAS;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<ConstraintF>;
    type SpongeVar = PoseidonSpongeVar<ConstraintF>;

    type AS = NarkAS<G, DummyCircuit<F>, Sponge>;
    type I = NarkASTestInput;
    type ASV = NarkASVerifierGadget<G, C, Sponge, SpongeVar>;

    #[test]
    pub fn test_initialization_no_zk() {
        crate::constraints::tests::test_initialization::<AS, I, ConstraintF, ASV>(
            &NarkASTestParams {
                num_inputs: 1,
                num_constraints: 10,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_initialization_zk() {
        crate::constraints::tests::test_initialization::<AS, I, ConstraintF, ASV>(
            &NarkASTestParams {
                num_inputs: 1,
                num_constraints: 10,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_no_zk() {
        crate::constraints::tests::test_simple_accumulation::<AS, I, ConstraintF, ASV>(
            &NarkASTestParams {
                num_inputs: 1,
                num_constraints: 10,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_zk() {
        crate::constraints::tests::test_simple_accumulation::<AS, I, ConstraintF, ASV>(
            &NarkASTestParams {
                num_inputs: 1,
                num_constraints: 10,
                make_zk: true,
            },
            1,
        );
    }
}
