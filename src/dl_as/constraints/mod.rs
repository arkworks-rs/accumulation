use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_poly_commit::ipa_pc;
use ark_poly_commit::ipa_pc::constraints::{
    CMCommitGadget, InnerProductArgPCGadget, SuccinctCheckPolynomialVar,
};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::FieldElementSize;
use ark_std::marker::PhantomData;
use std::ops::Mul;

pub mod data_structures;
pub use data_structures::*;

pub struct DLAccumulationSchemeGadget<G, C, S>
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

impl<G, C, S> DLAccumulationSchemeGadget<G, C, S>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    S: CryptographicSpongeVar<ConstraintF<G>>,
{
    #[tracing::instrument(target = "r1cs", skip(ck, linear_polynomial))]
    fn deterministic_commit_to_linear_polynomial(
        ck: &ipa_pc::constraints::CommitterKeyVar<G, C>,
        linear_polynomial: &[NNFieldVar<G>; 2],
    ) -> Result<FinalCommKeyVar<C>, SynthesisError> {
        let linear_polynomial_bits = linear_polynomial
            .into_iter()
            .map(|f| f.to_bits_le())
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        CMCommitGadget::<G, C>::commit(
            ck.comm_key.as_slice(),
            linear_polynomial_bits.as_slice(),
            None,
        )
    }

    #[tracing::instrument(target = "r1cs", skip(linear_polynomial, point))]
    fn evaluate_linear_polynomial(
        linear_polynomial: &[NNFieldVar<G>; 2],
        point: &NNFieldVar<G>,
    ) -> NNFieldVar<G> {
        (&linear_polynomial[1]).mul(point) + &linear_polynomial[0]
    }

    #[tracing::instrument(target = "r1cs", skip(cs, ipa_vk, inputs))]
    fn succinct_check_inputs<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        ipa_vk: &ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
        inputs: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
    ) -> Result<
        Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &'a FinalCommKeyVar<C>,
        )>,
        SynthesisError,
    > {
        let _test = SpongeVarForPC::<G, S>::new(cs.clone());
        inputs
            .into_iter()
            .map(|input| {
                let ipa_commitment = &input.ipa_commitment;
                let (succinct_check_result, check_polynomial) =
                    InnerProductArgPCGadget::<G, C, SpongeVarForPC<G, S>>::succinct_check(
                        ns!(cs, "succinct_check").cs(),
                        ipa_vk,
                        vec![ipa_commitment],
                        &input.point,
                        vec![&input.evaluation],
                        &input.ipa_proof,
                        &|_| NNFieldVar::<G>::one(),
                    )?;

                Ok((
                    succinct_check_result,
                    check_polynomial,
                    &input.ipa_proof.final_comm_key,
                ))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()
    }

    #[tracing::instrument(target = "r1cs", skip(sponge, check_polynomial))]
    fn absorb_check_polynomial_into_sponge(
        sponge: &mut SpongeVarForAccScheme<G, S>,
        check_polynomial: &SuccinctCheckPolynomialVar<G>,
        log_supported_degree: usize,
    ) -> Result<(), SynthesisError> {
        assert!(check_polynomial.0.len() <= log_supported_degree);
        let mut bytes_input = Vec::new();

        let elems = &check_polynomial.0;
        for i in 0..(log_supported_degree + 1) {
            if i < elems.len() {
                bytes_input.append(&mut (elems[i].to_bytes()?));
            } else {
                // Pad the check polynomial if necessary
                bytes_input.append(&mut NNFieldVar::<G>::zero().to_bytes()?);
            }
        }

        sponge.absorb(bytes_input.to_constraint_field()?.as_slice())?;
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(cs, ipa_vk, succinct_checks, _proof))]
    fn combine_succinct_checks_and_proof<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        ipa_vk: &ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
        succinct_checks: &'a Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &FinalCommKeyVar<C>,
        )>,
        _proof: &ProofVar<G, C>,
    ) -> Result<
        (
            Boolean<ConstraintF<G>>, // Combined succinct check results
            C,                       // Combined commitment
            Vec<(NNFieldVar<G>, &'a SuccinctCheckPolynomialVar<G>)>, // Addends to compute combined check polynomial
            NNFieldVar<G>,                                           // New challenge point
        ),
        SynthesisError,
    > {
        let supported_degree = ipa_vk.supported_degree;
        let log_supported_degree = ark_std::log2(supported_degree + 1) as usize;

        let mut linear_combination_challenge_sponge =
            SpongeVarForAccScheme::<G, S>::new(ns!(cs, "linear_combination_challenge_sponge").cs());
        // TODO: Reenable for hiding
        /*
        let random_coeffs = &proof.random_linear_polynomial_coeffs;
        linear_combination_challenge_sponge
            .absorb_bytes(random_coeffs[0].to_bytes()?.as_slice())?;
        linear_combination_challenge_sponge
            .absorb_bytes(random_coeffs[1].to_bytes()?.as_slice())?;
        linear_combination_challenge_sponge.absorb_bytes(
            proof
                .random_linear_polynomial_commitment
                .to_bytes()?
                .as_slice(),
        )?;
         */

        let _cost_absorbing_succinct_check_polys = cs.num_constraints();
        let mut combined_succinct_check_result = Boolean::TRUE;
        for (_, check_polynomial, commitment) in succinct_checks {
            if log_supported_degree > check_polynomial.0.len() {
                combined_succinct_check_result = Boolean::FALSE;
                continue;
            }

            Self::absorb_check_polynomial_into_sponge(
                &mut linear_combination_challenge_sponge,
                check_polynomial,
                log_supported_degree,
            )?;

            linear_combination_challenge_sponge
                .absorb(commitment.to_constraint_field()?.as_slice())?;
        }

        let (linear_combination_challenges, linear_combination_challenge_bitss) =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated { num_bits: 128 }; succinct_checks.len()]
                    .as_slice(),
            )?;

        // TODO: Revert for hiding
        //let mut combined_commitment = proof.random_linear_polynomial_commitment.clone();
        let mut combined_commitment = C::zero();

        let mut combined_check_polynomial_and_addends = Vec::with_capacity(succinct_checks.len());
        let mut addend_bitss = Vec::with_capacity(succinct_checks.len());

        for (
            ((succinct_check_result, check_polynomial, commitment), cur_challenge),
            cur_challenge_bits,
        ) in succinct_checks
            .into_iter()
            .zip(&linear_combination_challenges)
            .zip(&linear_combination_challenge_bitss)
        {
            combined_succinct_check_result =
                combined_succinct_check_result.and(&succinct_check_result)?;

            combined_commitment += &(commitment.scalar_mul_le(cur_challenge_bits.iter())?);

            combined_check_polynomial_and_addends.push((cur_challenge.clone(), check_polynomial));

            addend_bitss.push(cur_challenge_bits);
        }

        // TODO: Reenable for hiding
        /*
        let randomized_combined_commitment = ipa_vk
            .s
            .scalar_mul_le(proof.commitment_randomness.iter())?
            + &combined_commitment;
         */

        let randomized_combined_commitment = combined_commitment.clone();

        let mut challenge_point_sponge =
            SpongeVarForAccScheme::<G, S>::new(ns!(cs, "challenge_point_sponge").cs());
        challenge_point_sponge.absorb(combined_commitment.to_constraint_field()?.as_slice())?;

        for ((_, check_polynomial), linear_combination_challenge_bits) in
            combined_check_polynomial_and_addends
                .iter()
                .zip(&addend_bitss)
        {
            if log_supported_degree > (*check_polynomial).0.len() {
                combined_succinct_check_result = Boolean::FALSE;
                continue;
            }

            let linear_combination_challenge_bytes = linear_combination_challenge_bits
                .chunks(8)
                .map(UInt8::<ConstraintF<G>>::from_bits_le)
                .collect::<Vec<_>>();

            challenge_point_sponge.absorb(
                linear_combination_challenge_bytes
                    .to_constraint_field()?
                    .as_slice(),
            )?;

            Self::absorb_check_polynomial_into_sponge(
                &mut challenge_point_sponge,
                *check_polynomial,
                log_supported_degree,
            )?;
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])?
            .0
            .pop()
            .unwrap();

        Ok((
            combined_succinct_check_result,
            randomized_combined_commitment,
            combined_check_polynomial_and_addends,
            challenge_point,
        ))
    }

    #[tracing::instrument(target = "r1cs", skip(combined_check_polynomial_addends, point))]
    fn evaluate_combined_check_polynomials<'a>(
        combined_check_polynomial_addends: impl IntoIterator<
            Item = (NNFieldVar<G>, &'a SuccinctCheckPolynomialVar<G>),
        >,
        point: &NNFieldVar<G>,
    ) -> Result<NNFieldVar<G>, SynthesisError> {
        let mut eval = NNFieldVar::<G>::zero();
        for (scalar, polynomial) in combined_check_polynomial_addends {
            eval += &polynomial.evaluate(point)?.mul(&scalar);
        }

        Ok(eval)
    }

    #[tracing::instrument(
        target = "r1cs",
        skip(
            cs,
            verifier_key,
            input_instances,
            accumulator_instances,
            new_accumulator_instance,
            proof
        )
    )]
    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &VerifierKeyVar<G, C>,
        input_instances: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        accumulator_instances: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        new_accumulator_instance: &InputInstanceVar<G, C>,
        proof: &ProofVar<G, C>,
    ) -> Result<Boolean<<G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let mut verify_result = Boolean::TRUE;

        if new_accumulator_instance
            .ipa_commitment
            .shifted_comm
            .is_some()
        {
            return Ok(Boolean::FALSE);
        }

        // TODO: Revert for hiding
        // let linear_polynomial_commitment = Self::deterministic_commit_to_linear_polynomial(
        //     &verifier_key.ipa_ck_linear,
        //     &proof.random_linear_polynomial_coeffs,
        // )?;

        // verify_result = verify_result.and(
        //     &linear_polynomial_commitment
        //         .is_eq(&proof.random_linear_polynomial_commitment)?,
        // )?;

        // let cost = cs.num_constraints();
        let succinct_check_result = Self::succinct_check_inputs(
            ns!(cs, "succinct_check_results").cs(),
            &verifier_key.ipa_vk,
            input_instances.into_iter().chain(accumulator_instances),
        )?;
        // println!(
        //     "Cost of succinct_check_inputs: {:?}",
        //     cs.num_constraints() - cost
        // );

        // let cost = cs.num_constraints();
        let (
            combined_succinct_check_result,
            combined_commitment,
            combined_check_poly_addends,
            challenge,
        ) = Self::combine_succinct_checks_and_proof(
            ns!(cs, "combine_succinct_checks_and_proof").cs(),
            &verifier_key.ipa_vk,
            &succinct_check_result,
            &proof,
        )?;
        /*
        println!(
            "Cost of combine_succinct_checks: {:?}",
            cs.num_constraints() - cost
        );

         */

        verify_result = verify_result.and(&combined_succinct_check_result)?;

        verify_result = verify_result
            .and(&combined_commitment.is_eq(&new_accumulator_instance.ipa_commitment.comm)?)?;

        verify_result = verify_result.and(&challenge.is_eq(&new_accumulator_instance.point)?)?;

        let eval =
            Self::evaluate_combined_check_polynomials(combined_check_poly_addends, &challenge)?;
        /*
        println!(
            "Cost of evaluate_combined_check_polynomial: {:?}",
            cs.num_constraints() - cost
        );
        println!("Total constraint: {:?}", cs.num_constraints());

         */

        // TODO: Revert for hiding
        /*
        eval += Self::evaluate_linear_polynomial(
            &proof.random_linear_polynomial_coeffs,
            &challenge,
        );

         */

        verify_result = verify_result.and(&eval.is_eq(&new_accumulator_instance.evaluation)?)?;

        Ok(verify_result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::dl_as::constraints::{
        DLAccumulationSchemeGadget, InputInstanceVar, ProofVar, VerifierKeyVar,
    };
    use crate::dl_as::tests::DLAccumulationSchemeTestInput;
    use crate::dl_as::DLAccumulationScheme;
    use crate::tests::AccumulationSchemeTestInput;
    use crate::AidedAccumulationScheme;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::ns;
    use ark_relations::r1cs::ConstraintLayer;
    use ark_relations::r1cs::{ConstraintSystem, TracingMode};
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::CryptographicSponge;
    use ark_std::test_rng;
    use tracing_subscriber::layer::SubscriberExt;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;
    // type G = ark_ed_on_bls12_381::EdwardsAffine;
    // type C = ark_ed_on_bls12_381::constraints::EdwardsVar;
    // type F = ark_ed_on_bls12_381::Fr;
    // type ConstraintF = ark_ed_on_bls12_381::Fq;

    type AS = DLAccumulationScheme<
        G,
        DensePolynomial<F>,
        sha2::Sha512,
        rand_chacha::ChaChaRng,
        ConstraintF,
        PoseidonSponge<ConstraintF>,
    >;

    type I = DLAccumulationSchemeTestInput;

    #[test]
    pub fn basic() {
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

        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        tracing::subscriber::set_global_default(subscriber).unwrap();

        let cs = ConstraintSystem::<ConstraintF>::new_ref();

        let cs_init = ns!(cs, "init var").cs();
        let cost = cs.num_constraints();
        let vk = VerifierKeyVar::<G, C>::new_constant(cs_init.clone(), vk.clone()).unwrap();
        println!(
            "Cost of declaring verifier_key {:?}",
            cs.num_constraints() - cost
        );

        let cost = cs.num_constraints();
        let new_input_instance = InputInstanceVar::<G, C>::new_witness(cs_init.clone(), || {
            Ok(new_input.instance.clone())
        })
        .unwrap();
        println!("Cost of declaring input {:?}", cs.num_constraints() - cost);

        let cost = cs.num_constraints();
        let old_accumulator_instance =
            InputInstanceVar::<G, C>::new_witness(cs_init.clone(), || {
                Ok(old_accumulator.instance.clone())
            })
            .unwrap();

        println!(
            "Cost of declaring old accumulator {:?}",
            cs.num_constraints() - cost
        );

        let cost = cs.num_constraints();
        let new_accumulator_instance = InputInstanceVar::<G, C>::new_input(cs_init.clone(), || {
            Ok(new_accumulator.instance.clone())
        })
        .unwrap();

        println!(
            "Cost of declaring new accumulator {:?}",
            cs.num_constraints() - cost
        );

        let proof = ProofVar::<G, C>::new_witness(cs_init.clone(), || Ok(proof)).unwrap();

        DLAccumulationSchemeGadget::<G, C, PoseidonSpongeVar<ConstraintF>>::verify(
            ns!(cs, "dl_as_verify").cs(),
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

        if !cs.is_satisfied().unwrap() {
            println!("{}", cs.which_is_unsatisfied().unwrap().unwrap());
        }

        // println!("BEGIN");
        // for constraint in cs.constraint_names().unwrap() {
        //     println!("{:}", constraint)
        // }
        // println!("END");
    }
}
