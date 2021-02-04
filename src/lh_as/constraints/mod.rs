use crate::constraints::{ConstraintF, NNFieldVar};
use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_nonnative_field::NonNativeFieldMulResultVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::FieldElementSize;
use ark_std::ops::Mul;
use std::marker::PhantomData;

pub mod data_structures;
pub use data_structures::*;

pub struct LHAccumulationSchemeGadget<G, C, S>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    S: CryptographicSpongeVar<ConstraintF<G>>,
{
    pub _affine: PhantomData<G>,
    pub _curve: PhantomData<C>,
    pub _sponge: PhantomData<S>,
}

impl<G, C, S> LHAccumulationSchemeGadget<G, C, S>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    S: CryptographicSpongeVar<ConstraintF<G>>,
{
    #[tracing::instrument(target = "r1cs", skip(evaluations, challenge))]
    fn combine_evaluation<'a>(
        evaluations: impl IntoIterator<Item = &'a NNFieldVar<G>>,
        challenge: &[NNFieldVar<G>],
    ) -> Result<NNFieldVar<G>, SynthesisError> {
        let mut combined_evaluation =
            NonNativeFieldMulResultVar::<G::ScalarField, ConstraintF<G>>::zero();
        for (i, eval) in evaluations.into_iter().enumerate() {
            combined_evaluation += (&eval).mul_without_reduce(&challenge[i])?;
        }

        Ok(combined_evaluation.reduce()?)
    }

    #[tracing::instrument(target = "r1cs", skip(commitment, challenge_bytes))]
    fn combine_commitment<'a>(
        commitment: impl IntoIterator<Item = &'a C>,
        challenge_bytes: &[Vec<Boolean<ConstraintF<G>>>],
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = C::zero();
        for (i, comm) in commitment.into_iter().enumerate() {
            combined_commitment += &comm.scalar_mul_le(challenge_bytes[i].iter())?;
        }

        Ok(combined_commitment)
    }

    #[tracing::instrument(
        target = "r1cs",
        skip(
            cs,
            verifier_key,
            input_instance,
            accumulator_instance,
            new_accumulator_instance,
            proof
        )
    )]
    fn verify<'a>(
        cs: ConstraintSystemRef<<<G as AffineCurve>::BaseField as Field>::BasePrimeField>,
        verifier_key: &VerifierKeyVar<ConstraintF<G>>,
        input_instance: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        accumulator_instance: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        new_accumulator_instance: &InputInstanceVar<G, C>,
        proof: &ProofVar<G, C>,
    ) -> Result<Boolean<<G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let mut verify_result = Boolean::TRUE;

        let mut challenge_point_sponge = S::new(cs.clone());
        challenge_point_sponge.absorb(&[verifier_key.0.clone()])?;

        let mut commitment = Vec::new();
        for (input_instance, single_proof) in input_instance
            .into_iter()
            .chain(accumulator_instance)
            .zip(proof)
        {
            input_instance.absorb_into_sponge::<S>(&mut challenge_point_sponge)?;
            challenge_point_sponge.absorb(
                single_proof
                    .witness_commitment
                    .to_constraint_field()?
                    .as_slice(),
            )?;

            let eval_check_lhs: NNFieldVar<G> = &single_proof.eval - &input_instance.eval;
            let eval_check_rhs: NNFieldVar<G> = (&single_proof.witness_eval)
                .mul(&(&new_accumulator_instance.point - &input_instance.point));

            let eval_check = eval_check_lhs.is_eq(&eval_check_rhs)?;
            verify_result = verify_result.and(&eval_check)?;

            commitment.push(&input_instance.commitment);
        }

        let mut challenge_point_sponge_field_element_and_bits = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])?;

        let challenge_point = challenge_point_sponge_field_element_and_bits
            .0
            .pop()
            .unwrap();

        let challenge_point_bits = challenge_point_sponge_field_element_and_bits
            .1
            .pop()
            .unwrap();

        verify_result =
            verify_result.and(&challenge_point.is_eq(&new_accumulator_instance.point)?)?;

        let mut linear_combination_challenge_sponge = S::new(cs.clone());

        let challenge_point_bytes = challenge_point_bits
            .chunks(8)
            .map(|c| {
                if c.len() != 8 {
                    let mut padded_c = c.to_vec();
                    padded_c.resize_with(8, || Boolean::FALSE);
                    UInt8::<ConstraintF<G>>::from_bits_le(padded_c.as_slice())
                } else {
                    UInt8::<ConstraintF<G>>::from_bits_le(c)
                }
            })
            .collect::<Vec<_>>();

        linear_combination_challenge_sponge
            .absorb(challenge_point_bytes.to_constraint_field()?.as_slice())?;

        for single_proof in proof {
            linear_combination_challenge_sponge.absorb(
                single_proof
                    .eval
                    .to_bytes()?
                    .to_constraint_field()?
                    .as_slice(),
            )?;
            linear_combination_challenge_sponge.absorb(
                single_proof
                    .witness_eval
                    .to_bytes()?
                    .to_constraint_field()?
                    .as_slice(),
            )?;
        }

        let (linear_combination_challenge, linear_combination_challenge_bits) =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated { num_bits: 128 }; proof.len() * 2].as_slice(),
            )?;

        let combined_eval = Self::combine_evaluation(
            proof
                .into_iter()
                .map(|p| &p.eval)
                .chain(proof.into_iter().map(|p| &p.witness_eval)),
            linear_combination_challenge.as_slice(),
        )?;

        verify_result = verify_result.and(&combined_eval.is_eq(&new_accumulator_instance.eval)?)?;

        let combined_commitment = Self::combine_commitment(
            commitment
                .into_iter()
                .chain(proof.into_iter().map(|p| &p.witness_commitment)),
            linear_combination_challenge_bits.as_slice(),
        )?;

        verify_result =
            verify_result.and(&combined_commitment.is_eq(&new_accumulator_instance.commitment)?)?;

        Ok(verify_result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::lh_as::constraints::{
        InputInstanceVar, LHAccumulationSchemeGadget, ProofVar, VerifierKeyVar,
    };
    use crate::lh_as::tests::LHAidedAccumulationSchemeTestInput;
    use crate::lh_as::LHAidedAccumulationScheme;
    use crate::tests::AidedAccumulationSchemeTestInput;
    use crate::AidedAccumulationScheme;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_std::test_rng;

    /*
    type G = ark_ed_on_bls12_381::EdwardsAffine;
    type C = ark_ed_on_bls12_381::constraints::EdwardsVar;
    type F = ark_ed_on_bls12_381::Fr;
    type ConstraintF = ark_ed_on_bls12_381::Fq;
    */
    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;

    type AS =
        LHAidedAccumulationScheme<G, DensePolynomial<F>, ConstraintF, PoseidonSponge<ConstraintF>>;

    type I = LHAidedAccumulationSchemeTestInput;

    #[test]
    pub fn test() {
        let mut rng = test_rng();

        let (input_params, predicate_params, predicate_index) =
            <I as AidedAccumulationSchemeTestInput<AS>>::setup(&(), &mut rng);
        let pp = AS::generate(&mut rng).unwrap();
        let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();
        let mut inputs = <I as AidedAccumulationSchemeTestInput<AS>>::generate_inputs(
            &input_params,
            2,
            &mut rng,
        );
        let old_input = inputs.pop().unwrap();
        let new_input = inputs.pop().unwrap();

        let (old_accumulator, _) =
            AS::prove(&pk, vec![old_input.as_ref()], vec![], Some(&mut rng)).unwrap();
        let (new_accumulator, proof) = AS::prove(
            &pk,
            vec![new_input.as_ref()],
            vec![old_accumulator.as_ref()],
            Some(&mut rng),
        )
        .unwrap();

        assert!(AS::verify(
            &vk,
            vec![&new_input.instance],
            vec![&old_accumulator.instance],
            &new_accumulator.instance,
            &proof
        )
        .unwrap());

        let cs = ConstraintSystem::<ConstraintF>::new_ref();
        let vk = VerifierKeyVar::<ConstraintF>::new_constant(cs.clone(), vk.clone()).unwrap();

        let new_input_instance =
            InputInstanceVar::<G, C>::new_witness(cs.clone(), || Ok(new_input.instance.clone()))
                .unwrap();

        let old_accumulator_instance = InputInstanceVar::<G, C>::new_witness(cs.clone(), || {
            Ok(old_accumulator.instance.clone())
        })
        .unwrap();

        let new_accumulator_instance = InputInstanceVar::<G, C>::new_input(cs.clone(), || {
            Ok(new_accumulator.instance.clone())
        })
        .unwrap();

        let proof = ProofVar::<G, C>::new_witness(cs.clone(), || Ok(proof)).unwrap();

        LHAccumulationSchemeGadget::<G, C, PoseidonSpongeVar<ConstraintF>>::verify(
            cs.clone(),
            &vk,
            vec![&new_input_instance],
            vec![&old_accumulator_instance],
            &new_accumulator_instance,
            &proof,
        )
        .unwrap()
        .enforce_equal(&Boolean::TRUE)
        .unwrap();

        println!("Num constaints: {:}", cs.num_constraints());
        println!("Num instance: {:}", cs.num_instance_variables());
        println!("Num witness: {:}", cs.num_witness_variables());
        /*
        if !cs.is_satisfied().unwrap() {
            println!("{}", cs.which_is_unsatisfied().unwrap().unwrap());
        }

         */

        assert!(cs.is_satisfied().unwrap());
    }
}
