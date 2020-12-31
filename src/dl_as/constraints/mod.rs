use ark_ec::AffineCurve;
use ark_ff::{Field, One};
use ark_marlin::fiat_shamir::constraints::{AlgebraicSpongeVar, FiatShamirRngVar};
use ark_marlin::fiat_shamir::{AlgebraicSponge, FiatShamirRng};
use ark_poly_commit::ipa_pc;
use ark_poly_commit::ipa_pc::constraints::{
    CMCommitGadget, InnerProductArgPCGadget, SuccinctCheckPolynomialVar,
};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::marker::PhantomData;
use std::ops::Mul;

pub mod data_structures;
pub use data_structures::*;

pub struct DLAccumulationSchemeGadget<G, C, S, SV>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    S: FiatShamirRng<G::ScalarField, ConstraintF<G>>,
    SV: FiatShamirRngVar<G::ScalarField, ConstraintF<G>, S>,
{
    pub _affine: PhantomData<G>,
    pub _curve: PhantomData<C>,
    pub _sponge: PhantomData<S>,
    pub _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> DLAccumulationSchemeGadget<G, C, S, SV>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    S: FiatShamirRng<G::ScalarField, ConstraintF<G>>,
    SV: FiatShamirRngVar<G::ScalarField, ConstraintF<G>, S>,
{
    fn deterministic_commit_to_linear_polynomial_var(
        ck_var: &ipa_pc::constraints::CommitterKeyVar<G, C>,
        linear_polynomial_var: &[NNFieldVar<G>; 2],
    ) -> Result<FinalCommKeyVar<C>, SynthesisError> {
        let linear_polynomial_bits_var = linear_polynomial_var
            .into_iter()
            .map(|f| f.to_bits_le())
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        CMCommitGadget::<G, C>::commit(
            ck_var.comm_key_var.as_slice(),
            linear_polynomial_bits_var.as_slice(),
            None,
        )
    }

    fn evaluate_linear_polynomial_var(
        linear_polynomial_var: &[NNFieldVar<G>; 2],
        point_var: &NNFieldVar<G>,
    ) -> NNFieldVar<G> {
        (&linear_polynomial_var[1]).mul(point_var) + &linear_polynomial_var[0]
    }

    fn succinct_check_input_vars<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        ipa_vk_var: &ipa_pc::constraints::VerifierKeyVar<G, C>,
        input_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
    ) -> Result<
        Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &'a FinalCommKeyVar<C>,
        )>,
        SynthesisError,
    > {
        input_vars
            .into_iter()
            .map(|input_var| {
                let ipa_commitment_var = &input_var.ipa_commitment_var;
                let (succinct_check_result_var, check_polynomial_var) =
                    InnerProductArgPCGadget::<G, C, S, SpongeVarForPC<G, S, SV>>::succinct_check(
                        ns!(cs, "succinct_check").cs(),
                        ipa_vk_var,
                        vec![ipa_commitment_var],
                        &input_var.point_var,
                        vec![&input_var.evaluation_var],
                        &input_var.ipa_proof_var,
                        &|_| NNFieldVar::<G>::one(),
                    )?;

                Ok((
                    succinct_check_result_var,
                    check_polynomial_var,
                    &input_var.ipa_proof_var.final_comm_key_var,
                ))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()
    }

    fn absorb_check_polynomial_var_into_sponge_var(
        sponge_var: &mut SpongeVarForAccScheme<G, S, SV>,
        check_polynomial_var: &SuccinctCheckPolynomialVar<G>,
        log_supported_degree: usize,
    ) -> Result<(), SynthesisError> {
        assert!(check_polynomial_var.0.len() <= log_supported_degree);
        let mut bytes_input_var = Vec::new();

        let elem_vars = &check_polynomial_var.0;
        for i in 0..(log_supported_degree + 1) {
            if i < elem_vars.len() {
                bytes_input_var.append(&mut (elem_vars[i].to_bytes()?));
            } else {
                // Pad the check polynomial if necessary
                bytes_input_var.append(&mut NNFieldVar::<G>::zero().to_bytes()?);
            }
        }

        sponge_var.absorb_bytes(bytes_input_var.as_slice())?;

        Ok(())
    }

    fn combine_succinct_check_vars_and_proof_var<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        ipa_vk_var: &ipa_pc::constraints::VerifierKeyVar<G, C>,
        succinct_check_vars: &'a Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &FinalCommKeyVar<C>,
        )>,
        proof_var: &ProofVar<G, C>,
    ) -> Result<
        (
            Boolean<ConstraintF<G>>, // Combined succinct check results
            C,                       // Combined commitment
            Vec<(NNFieldVar<G>, &'a SuccinctCheckPolynomialVar<G>)>, // Addends to compute combined check polynomial
            NNFieldVar<G>,                                           // New challenge point
        ),
        SynthesisError,
    > {
        let supported_degree = ipa_vk_var.supported_degree();
        let log_supported_degree = ark_std::log2(supported_degree + 1) as usize;

        let mut linear_combination_challenge_sponge_var = SpongeVarForAccScheme::<G, S, SV>::new(
            ns!(cs, "linear_combination_challenge_sponge_var").cs(),
        );
        // TODO: Reenable for hiding
        /*
        let random_coeff_vars = &proof_var.random_linear_polynomial_coeff_vars;
        linear_combination_challenge_sponge_var
            .absorb_bytes(random_coeff_vars[0].to_bytes()?.as_slice())?;
        linear_combination_challenge_sponge_var
            .absorb_bytes(random_coeff_vars[1].to_bytes()?.as_slice())?;
        linear_combination_challenge_sponge_var.absorb_bytes(
            proof_var
                .random_linear_polynomial_commitment_var
                .to_bytes()?
                .as_slice(),
        )?;
         */

        let mut combined_succinct_check_result_var = Boolean::TRUE;
        for (_, check_polynomial_var, commitment_var) in succinct_check_vars {
            if log_supported_degree > check_polynomial_var.0.len() {
                combined_succinct_check_result_var = Boolean::FALSE;
                continue;
            }

            Self::absorb_check_polynomial_var_into_sponge_var(
                &mut linear_combination_challenge_sponge_var,
                check_polynomial_var,
                log_supported_degree,
            )?;

            linear_combination_challenge_sponge_var
                .absorb_bytes(commitment_var.to_bytes()?.as_slice())?;
        }

        let linear_combination_challenge_var = linear_combination_challenge_sponge_var
            .squeeze_field_elements(1)?
            .pop()
            .unwrap();

        // TODO: Revert for hiding
        //let mut combined_commitment_var = proof_var.random_linear_polynomial_commitment_var.clone();
        let mut combined_commitment_var = C::zero();

        let mut combined_check_polynomial_and_addend_vars =
            Vec::with_capacity(succinct_check_vars.len());
        let mut addend_bytes_vars = Vec::with_capacity(succinct_check_vars.len());

        let mut cur_challenge_var = linear_combination_challenge_var.clone();
        for (succinct_check_result_var, check_polynomial_var, commitment_var) in succinct_check_vars
        {
            combined_succinct_check_result_var =
                combined_succinct_check_result_var.and(&succinct_check_result_var)?;

            let cur_challenge_bytes_var = cur_challenge_var.to_bytes()?;
            combined_commitment_var +=
                &(commitment_var.scalar_mul_le(cur_challenge_bytes_var.to_bits_le()?.iter())?);
            combined_check_polynomial_and_addend_vars
                .push((cur_challenge_var.clone(), check_polynomial_var));
            addend_bytes_vars.push(cur_challenge_bytes_var);

            cur_challenge_var *= &linear_combination_challenge_var;
        }

        // TODO: Reenable for hiding
        /*
        let randomized_combined_commitment_var = ipa_vk_var
            .s_var
            .scalar_mul_le(proof_var.commitment_randomness_var.iter())?
            + &combined_commitment_var;
         */

        let randomized_combined_commitment_var = combined_commitment_var.clone();

        let mut challenge_point_sponge_var =
            SpongeVarForAccScheme::<G, S, SV>::new(ns!(cs, "challenge_point_sponge_var").cs());
        challenge_point_sponge_var.absorb_bytes(combined_commitment_var.to_bytes()?.as_slice())?;

        for ((_, check_polynomial_var), linear_combination_challenge_bytes_var) in
            combined_check_polynomial_and_addend_vars
                .iter()
                .zip(&addend_bytes_vars)
        {
            if log_supported_degree > (*check_polynomial_var).0.len() {
                combined_succinct_check_result_var = Boolean::FALSE;
                continue;
            }

            challenge_point_sponge_var
                .absorb_bytes(linear_combination_challenge_bytes_var.as_slice())?;

            Self::absorb_check_polynomial_var_into_sponge_var(
                &mut challenge_point_sponge_var,
                *check_polynomial_var,
                log_supported_degree,
            )?;
        }

        let challenge_point_var = challenge_point_sponge_var
            .squeeze_field_elements(1)?
            .pop()
            .unwrap();

        Ok((
            combined_succinct_check_result_var,
            randomized_combined_commitment_var,
            combined_check_polynomial_and_addend_vars,
            challenge_point_var,
        ))
    }

    fn evaluate_combined_check_polynomial_vars<'a>(
        combined_check_polynomial_addend_vars: impl IntoIterator<
            Item = (NNFieldVar<G>, &'a SuccinctCheckPolynomialVar<G>),
        >,
        point_var: &NNFieldVar<G>,
    ) -> Result<NNFieldVar<G>, SynthesisError> {
        let mut eval_var = NNFieldVar::<G>::zero();
        for (scalar_var, polynomial_var) in combined_check_polynomial_addend_vars {
            eval_var += &polynomial_var.evaluate(point_var)?.mul(&scalar_var);
        }

        Ok(eval_var)
    }

    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key_var: &VerifierKeyVar<G, C>,
        input_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        accumulator_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        new_accumulator_instance_var: &InputInstanceVar<G, C>,
        proof_var: &ProofVar<G, C>,
    ) -> Result<Boolean<<G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let mut verify_result_var = Boolean::TRUE;

        if new_accumulator_instance_var
            .ipa_commitment_var
            .shifted_comm_var
            .is_some()
        {
            return Ok(Boolean::FALSE);
        }

        // TODO: Revert for hiding
        /*
        let linear_polynomial_commitment_var = Self::deterministic_commit_to_linear_polynomial_var(
            &verifier_key_var.ipa_ck_linear_var,
            &proof_var.random_linear_polynomial_coeff_vars,
        )?;

        verify_result_var = verify_result_var.and(
            &linear_polynomial_commitment_var
                .is_eq(&proof_var.random_linear_polynomial_commitment_var)?,
        )?;

         */

        let succinct_check_result_var = Self::succinct_check_input_vars(
            ns!(cs, "succinct_check_results_var").cs(),
            &verifier_key_var.ipa_vk_var,
            input_instance_vars
                .into_iter()
                .chain(accumulator_instance_vars),
        )?;

        let (
            combined_succinct_check_result_var,
            combined_commitment_var,
            combined_check_poly_addend_vars,
            challenge_var,
        ) = Self::combine_succinct_check_vars_and_proof_var(
            ns!(cs, "combine_succinct_check_vars_and_proof_var").cs(),
            &verifier_key_var.ipa_vk_var,
            &succinct_check_result_var,
            &proof_var,
        )?;

        verify_result_var = verify_result_var.and(&combined_succinct_check_result_var)?;

        verify_result_var = verify_result_var.and(
            &combined_commitment_var
                .is_eq(&new_accumulator_instance_var.ipa_commitment_var.comm_var)?,
        )?;

        verify_result_var = verify_result_var
            .and(&challenge_var.is_eq(&new_accumulator_instance_var.point_var)?)?;

        let mut eval_var = Self::evaluate_combined_check_polynomial_vars(
            combined_check_poly_addend_vars,
            &challenge_var,
        )?;

        // TODO: Revert for hiding
        /*
        eval_var += Self::evaluate_linear_polynomial_var(
            &proof_var.random_linear_polynomial_coeff_vars,
            &challenge_var,
        );

         */

        verify_result_var = verify_result_var
            .and(&eval_var.is_eq(&new_accumulator_instance_var.evaluation_var)?)?;

        verify_result_var.enforce_equal(&Boolean::TRUE);
        println!("{}", cs.which_is_unsatisfied().unwrap().unwrap());
        Ok(verify_result_var)
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
    use ark_marlin::fiat_shamir::constraints::{FiatShamirAlgebraicSpongeRngVar, FiatShamirRngVar};
    use ark_marlin::fiat_shamir::poseidon::constraints::PoseidonSpongeVar;
    use ark_marlin::fiat_shamir::poseidon::PoseidonSponge;
    use ark_marlin::fiat_shamir::FiatShamirAlgebraicSpongeRng;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::ns;
    use ark_relations::r1cs::ConstraintLayer;
    use ark_relations::r1cs::{ConstraintSystem, TracingMode};
    use ark_sponge::poseidon::PoseidonSpongeWrapper;
    use ark_sponge::CryptographicSponge;
    use ark_std::test_rng;
    use tracing_subscriber::layer::SubscriberExt;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;

    type AS = DLAccumulationScheme<
        G,
        DensePolynomial<F>,
        sha2::Sha512,
        rand_chacha::ChaChaRng,
        PoseidonSpongeWrapper<F, ConstraintF>,
    >;

    type I = DLAccumulationSchemeTestInput;

    type Poseidon = FiatShamirAlgebraicSpongeRng<F, ConstraintF, PoseidonSponge<ConstraintF>>;
    type PoseidonVar = FiatShamirAlgebraicSpongeRngVar<
        F,
        ConstraintF,
        PoseidonSponge<ConstraintF>,
        PoseidonSpongeVar<ConstraintF>,
    >;

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
        let vk_var = VerifierKeyVar::<G, C>::new_input(cs_init.clone(), || Ok(vk.clone())).unwrap();

        let new_input_instance_var =
            InputInstanceVar::<G, C>::new_input(cs_init.clone(), || Ok(new_input.instance.clone()))
                .unwrap();

        let old_accumulator_instance_var =
            InputInstanceVar::<G, C>::new_input(cs_init.clone(), || {
                Ok(old_accumulator.instance.clone())
            })
            .unwrap();

        let new_accumulator_instance_var =
            InputInstanceVar::<G, C>::new_input(cs_init.clone(), || {
                Ok(new_accumulator.instance.clone())
            })
            .unwrap();

        let proof_var = ProofVar::<G, C>::new_witness(cs_init.clone(), || Ok(proof)).unwrap();

        DLAccumulationSchemeGadget::<G, C, Poseidon, PoseidonVar>::verify(
            ns!(cs, "dl_as_verify").cs(),
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

        println!("{}", cs.which_is_unsatisfied().unwrap().unwrap());
        assert!(cs.is_satisfied().unwrap());

        /*
        for constraint in cs.constraint_names().unwrap() {
            println!("{:}", constraint)
        }

         */
    }
}
