use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_nonnative_field::NonNativeFieldMulResultVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{R1CSVar, ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget};
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
    #[tracing::instrument(target = "r1cs", skip(evaluations_var, challenge_vars))]
    fn combine_evaluation_vars<'a>(
        evaluations_var: impl IntoIterator<Item = &'a NNFieldVar<G>>,
        challenge_vars: &[NNFieldVar<G>],
    ) -> Result<NNFieldVar<G>, SynthesisError> {
        let mut combined_evaluation_vars =
            NonNativeFieldMulResultVar::<G::ScalarField, ConstraintF<G>>::zero();
        for (i, eval_var) in evaluations_var.into_iter().enumerate() {
            combined_evaluation_vars += (&eval_var).mul_without_reduce(&challenge_vars[i])?;
        }

        Ok(combined_evaluation_vars.reduce()?)
    }

    #[tracing::instrument(target = "r1cs", skip(commitment_vars, challenge_bytes_vars))]
    fn combine_commitment_vars<'a>(
        commitment_vars: impl IntoIterator<Item = &'a C>,
        challenge_bytes_vars: &[Vec<Boolean<ConstraintF<G>>>],
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment_var = C::zero();
        for (i, comm_var) in commitment_vars.into_iter().enumerate() {
            combined_commitment_var += &comm_var.scalar_mul_le(challenge_bytes_vars[i].iter())?;
        }

        Ok(combined_commitment_var)
    }

    #[tracing::instrument(
        target = "r1cs",
        skip(
            cs,
            verifier_key_var,
            input_instance_vars,
            accumulator_instance_vars,
            new_accumulator_instance_var,
            proof_var
        )
    )]
    fn verify<'a>(
        cs: ConstraintSystemRef<<<G as AffineCurve>::BaseField as Field>::BasePrimeField>,
        verifier_key_var: &VerifierKeyVar<ConstraintF<G>>,
        input_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        accumulator_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        new_accumulator_instance_var: &InputInstanceVar<G, C>,
        proof_var: &ProofVar<G, C>,
    ) -> Result<Boolean<<G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let mut verify_result_var = Boolean::TRUE;

        let mut challenge_point_sponge_var = S::new(cs.clone());
        challenge_point_sponge_var.absorb(&[verifier_key_var.0.clone()])?;

        let mut commitment_vars = Vec::new();
        for (input_instance_var, single_proof_var) in input_instance_vars
            .into_iter()
            .chain(accumulator_instance_vars)
            .zip(proof_var)
        {
            input_instance_var.absorb_into_sponge::<S>(&mut challenge_point_sponge_var)?;
            challenge_point_sponge_var.absorb(
                single_proof_var
                    .witness_commitment_var
                    .to_constraint_field()?
                    .as_slice(),
            )?;

            let eval_check_lhs_var: NNFieldVar<G> =
                &single_proof_var.eval_var - &input_instance_var.eval_var;
            let eval_check_rhs_var: NNFieldVar<G> = (&single_proof_var.witness_eval_var)
                .mul(&(&new_accumulator_instance_var.point_var - &input_instance_var.point_var));

            let eval_check_var = eval_check_lhs_var.is_eq(&eval_check_rhs_var)?;
            verify_result_var = verify_result_var.and(&eval_check_var)?;

            commitment_vars.push(&input_instance_var.commitment_var);
        }

        let mut challenge_point_sponge_field_element_and_bits = challenge_point_sponge_var
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])?;

        let challenge_point_var = challenge_point_sponge_field_element_and_bits
            .0
            .pop()
            .unwrap();

        let mut challenge_point_bits_var = challenge_point_sponge_field_element_and_bits
            .1
            .pop()
            .unwrap();

        verify_result_var = verify_result_var
            .and(&challenge_point_var.is_eq(&new_accumulator_instance_var.point_var)?)?;

        let mut linear_combination_challenge_sponge_var = S::new(cs.clone());

        let challenge_point_bytes_var = challenge_point_bits_var
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

        linear_combination_challenge_sponge_var
            .absorb(challenge_point_bytes_var.to_constraint_field()?.as_slice())?;

        for single_proof_var in proof_var {
            linear_combination_challenge_sponge_var.absorb(
                single_proof_var
                    .eval_var
                    .to_bytes()?
                    .to_constraint_field()?
                    .as_slice(),
            )?;
            linear_combination_challenge_sponge_var.absorb(
                single_proof_var
                    .witness_eval_var
                    .to_bytes()?
                    .to_constraint_field()?
                    .as_slice(),
            )?;
        }

        let (linear_combination_challenge_vars, linear_combination_challenge_bits_vars) = linear_combination_challenge_sponge_var
            .squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated { num_bits: 128 }; proof_var.len() * 2].as_slice(),
            )?;

        let combined_eval_var = Self::combine_evaluation_vars(
            proof_var
                .into_iter()
                .map(|p| &p.eval_var)
                .chain(proof_var.into_iter().map(|p| &p.witness_eval_var)),
            linear_combination_challenge_vars.as_slice(),
        )?;

        verify_result_var = verify_result_var
            .and(&combined_eval_var.is_eq(&new_accumulator_instance_var.eval_var)?)?;

        let combined_commitment_var = Self::combine_commitment_vars(
            commitment_vars
                .into_iter()
                .chain(proof_var.into_iter().map(|p| &p.witness_commitment_var)),
            linear_combination_challenge_bits_vars.as_slice()
        )?;

        verify_result_var = verify_result_var
            .and(&combined_commitment_var.is_eq(&new_accumulator_instance_var.commitment_var)?)?;

        Ok(verify_result_var)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::lh_as::constraints::{
        InputInstanceVar, LHAccumulationSchemeGadget, ProofVar, VerifierKeyVar,
    };
    use crate::lh_as::tests::LHAidedAccumulationSchemeTestInput;
    use crate::lh_as::LHAidedAccumulationScheme;
    use crate::tests::AccumulationSchemeTestInput;
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
            <I as AccumulationSchemeTestInput<AS>>::setup(&(), &mut rng);
        let pp = AS::generate(&mut rng).unwrap();
        let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();
        let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);
        let old_input = inputs.pop().unwrap();
        let new_input = inputs.pop().unwrap();

        let (old_accumulator, _) =
            AS::prove(&pk, vec![&old_input], vec![], Some(&mut rng)).unwrap();
        let (new_accumulator, proof) = AS::prove(
            &pk,
            vec![&new_input],
            vec![&old_accumulator],
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
        let vk_var =
            VerifierKeyVar::<ConstraintF>::new_witness(cs.clone(), || Ok(vk.clone())).unwrap();

        let new_input_instance_var =
            InputInstanceVar::<G, C>::new_witness(cs.clone(), || Ok(new_input.instance.clone()))
                .unwrap();

        let old_accumulator_instance_var =
            InputInstanceVar::<G, C>::new_witness(cs.clone(), || {
                Ok(old_accumulator.instance.clone())
            })
            .unwrap();

        let new_accumulator_instance_var = InputInstanceVar::<G, C>::new_input(cs.clone(), || {
            Ok(new_accumulator.instance.clone())
        })
        .unwrap();

        let proof_var = ProofVar::<G, C>::new_witness(cs.clone(), || Ok(proof)).unwrap();

        LHAccumulationSchemeGadget::<G, C, PoseidonSpongeVar<ConstraintF>>::verify(
            cs.clone(),
            &vk_var,
            vec![&new_input_instance_var],
            vec![&old_accumulator_instance_var],
            &new_accumulator_instance_var,
            &proof_var,
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
