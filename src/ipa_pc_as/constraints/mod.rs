use crate::constraints::{ASVerifierGadget, AtomicASVerifierGadget};
use crate::ipa_pc_as::{
    ASForIpaPCDomain, AtomicASForInnerProductArgPC, InputInstance, IpaPCDomain,
};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::{Field, Zero};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly_commit::ipa_pc::constraints::{
    CMCommitGadget, IpaPCSuccinctCheckGadget, SuccinctCheckPolynomialVar,
};
use ark_poly_commit::{ipa_pc, LabeledCommitment, PolynomialLabel};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::domain_separated::constraints::DomainSeparatedSpongeVar;
use ark_sponge::domain_separated::DomainSeparatedSponge;
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::vec;
use ark_r1cs_std::alloc::AllocVar;
use ark_std::vec::Vec;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
pub struct AtomicASForIpaPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    _affine: PhantomData<G>,
    _curve: PhantomData<C>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> AtomicASForIpaPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    /// Computes a deterministic IpaPC commitment to a linear polynomial.
    #[tracing::instrument(target = "r1cs", skip(ck, linear_polynomial))]
    fn deterministic_commit_to_linear_polynomial(
        ck: &ipa_pc::constraints::VerifierKeyVar<G, C>,
        linear_polynomial: &[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>; 2],
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

    /// Evaluates a linear polynomial at a point.
    #[tracing::instrument(target = "r1cs", skip(linear_polynomial, point))]
    fn evaluate_linear_polynomial(
        linear_polynomial: &[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>; 2],
        point: &NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
    ) -> NonNativeFieldVar<G::ScalarField, ConstraintF<G>> {
        (&linear_polynomial[1]).mul(point) + &linear_polynomial[0]
    }

    /// Computes succinct check on each input.
    #[tracing::instrument(target = "r1cs", skip(cs, ipa_vk, inputs))]
    fn succinct_check_inputs<'a, I: IntoIterator<Item = &'a InputInstanceVar<G, C>>>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        ipa_vk: &ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
        inputs: I,
    ) -> Result<
        Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &'a FinalCommKeyVar<C>,
        )>,
        SynthesisError,
    > {
        inputs
            .into_iter()
            .map(|input| {
                let ipa_commitment = &input.ipa_commitment;
                let (succinct_check_result, check_polynomial) = IpaPCSuccinctCheckGadget::<
                    G,
                    C,
                    DomainSeparatedSponge<ConstraintF<G>, S, IpaPCDomain>,
                    DomainSeparatedSpongeVar<ConstraintF<G>, S, SV, IpaPCDomain>,
                >::succinct_check(
                    ns!(cs, "succinct_check").cs(),
                    ipa_vk,
                    vec![ipa_commitment],
                    &input.point,
                    vec![&input.evaluation],
                    &input.ipa_proof,
                    &|_| NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::one(),
                )?;

                Ok((
                    succinct_check_result,
                    check_polynomial,
                    &input.ipa_proof.final_comm_key,
                ))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()
    }

    /// Absorbs an IpaPC succinct check polynomial into a sponge.
    #[tracing::instrument(target = "r1cs", skip(sponge, check_polynomial))]
    fn absorb_succinct_check_polynomial_into_sponge(
        sponge: &mut DomainSeparatedSpongeVar<ConstraintF<G>, S, SV, ASForIpaPCDomain>,
        check_polynomial: &SuccinctCheckPolynomialVar<G>,
    ) -> Result<(), SynthesisError> {
        let mut bytes_input = Vec::new();
        for elem in &check_polynomial.0 {
            bytes_input.append(&mut elem.to_bytes()?);
        }

        sponge.absorb(&bytes_input)?;
        Ok(())
    }

    /// Combines succinct check polynomials and final commitment keys from the succinct check
    /// outputs. Randomizes the combined commitment if the proof exists.
    #[tracing::instrument(target = "r1cs", skip(ipa_vk, succinct_checks, proof, as_sponge))]
    fn combine_succinct_check_polynomials_and_commitments<'a>(
        ipa_vk: &ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
        succinct_checks: &'a Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &FinalCommKeyVar<C>,
        )>,
        proof: &ProofVar<G, C>,
        as_sponge: DomainSeparatedSpongeVar<ConstraintF<G>, S, SV, ASForIpaPCDomain>,
    ) -> Result<
        (
            Boolean<ConstraintF<G>>, // Combined succinct check results
            C,                       // Combined commitment
            C,                       // Randomized combined commitment
            Vec<(
                (
                    NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
                    Vec<Boolean<ConstraintF<G>>>,
                ), // Coefficient and its bits
                &'a SuccinctCheckPolynomialVar<G>,
            )>, // Addends to compute combined check polynomial
        ),
        SynthesisError,
    > {
        let supported_degree = ipa_vk.supported_degree;
        let log_supported_degree = ark_std::log2(supported_degree + 1) as usize;

        let mut linear_combination_challenge_sponge = as_sponge.clone();

        if let Some(randomness) = proof.randomness.as_ref() {
            let random_coeffs = &randomness.random_linear_polynomial_coeffs;
            absorb_gadget!(
                &mut linear_combination_challenge_sponge,
                random_coeffs[0].to_bytes()?,
                random_coeffs[1].to_bytes()?,
                randomness.random_linear_polynomial_commitment
            );
        }

        let mut combined_succinct_check_result = Boolean::TRUE;
        for (_, check_polynomial, commitment) in succinct_checks {
            if log_supported_degree > check_polynomial.0.len() {
                combined_succinct_check_result = Boolean::FALSE;
                continue;
            }

            Self::absorb_succinct_check_polynomial_into_sponge(
                &mut linear_combination_challenge_sponge,
                check_polynomial,
            )?;

            linear_combination_challenge_sponge.absorb(&commitment)?;
        }

        let (linear_combination_challenges, linear_combination_challenge_bits) =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); succinct_checks.len()].as_slice(),
            )?;

        let mut combined_commitment = if let Some(randomness) = proof.randomness.as_ref() {
            randomness.random_linear_polynomial_commitment.clone()
        } else {
            C::zero()
        };

        let mut combined_check_polynomial_addends = Vec::with_capacity(succinct_checks.len());
        for (
            ((succinct_check_result, check_polynomial, commitment), cur_challenge),
            cur_challenge_bits,
        ) in succinct_checks
            .into_iter()
            .zip(linear_combination_challenges)
            .zip(linear_combination_challenge_bits)
        {
            combined_succinct_check_result =
                combined_succinct_check_result.and(&succinct_check_result)?;

            combined_commitment += &(commitment.scalar_mul_le(cur_challenge_bits.iter())?);
            combined_check_polynomial_addends
                .push(((cur_challenge, cur_challenge_bits), check_polynomial));
        }

        let randomized_combined_commitment = if let Some(randomness) = proof.randomness.as_ref() {
            ipa_vk
                .s
                .scalar_mul_le(randomness.commitment_randomness.iter())?
                + &combined_commitment
        } else {
            combined_commitment.clone()
        };

        Ok((
            combined_succinct_check_result,
            combined_commitment,
            randomized_combined_commitment,
            combined_check_polynomial_addends,
        ))
    }

    /// Compute the new opening point for the accumulator instance.
    fn compute_new_challenge<'a>(
        as_sponge: DomainSeparatedSpongeVar<ConstraintF<G>, S, SV, ASForIpaPCDomain>,
        combined_commitment: &C,
        combined_check_polynomial_addends: &Vec<(
            (
                NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
                Vec<Boolean<ConstraintF<G>>>,
            ),
            &'a SuccinctCheckPolynomialVar<G>,
        )>,
        random_linear_polynomial: Option<&[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>; 2]>,
    ) -> Result<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>, SynthesisError> {
        let mut challenge_point_sponge = as_sponge;
        challenge_point_sponge.absorb(&combined_commitment)?;

        challenge_point_sponge.absorb(
            &random_linear_polynomial
                .map(|p| {
                    let mut bytes = p[0].to_bytes()?;
                    bytes.append(&mut p[1].to_bytes()?);
                    Ok(bytes)
                })
                .transpose()?,
        )?;

        for ((_, linear_combination_challenge_bits), check_polynomial) in
            combined_check_polynomial_addends
        {
            let linear_combination_challenge_bytes = linear_combination_challenge_bits
                .chunks(8)
                .map(UInt8::<ConstraintF<G>>::from_bits_le)
                .collect::<Vec<_>>();

            challenge_point_sponge.absorb(&linear_combination_challenge_bytes)?;

            Self::absorb_succinct_check_polynomial_into_sponge(
                &mut challenge_point_sponge,
                *check_polynomial,
            )?;
        }

        Ok(challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])?
            .0
            .pop()
            .unwrap())
    }

    /// Evaluates the linear combination of succinct check polynomials at a point.
    #[tracing::instrument(target = "r1cs", skip(combined_check_polynomial_addends, point))]
    fn evaluate_combined_check_polynomials<'a>(
        combined_check_polynomial_addends: &Vec<(
            (
                NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
                Vec<Boolean<ConstraintF<G>>>,
            ),
            &'a SuccinctCheckPolynomialVar<G>,
        )>,
        point: &NonNativeFieldVar<G::ScalarField, ConstraintF<G>>,
        random_linear_polynomial: Option<&[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>; 2]>,
    ) -> Result<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>, SynthesisError> {
        let mut eval = random_linear_polynomial
            .map(|p| Self::evaluate_linear_polynomial(p, point))
            .unwrap_or_else(|| NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::zero());

        for ((scalar, _), polynomial) in combined_check_polynomial_addends {
            eval += &polynomial.evaluate(point)?.mul(scalar);
        }

        Ok(eval)
    }
}

impl<G, C, S, SV> ASVerifierGadget<ConstraintF<G>, AtomicASForInnerProductArgPC<G, S>>
    for AtomicASForIpaPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    type VerifierKey = VerifierKeyVar<G, C>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = InputInstanceVar<G, C>;
    type Proof = ProofVar<G, C>;

    #[tracing::instrument(
        target = "r1cs",
        skip(
            cs,
            verifier_key,
            input_instances,
            old_accumulator_instances,
            new_accumulator_instance,
            proof,
            sponge
        )
    )]
    fn verify<
        'a,
        UnusedS: CryptographicSponge<ConstraintF<G>>,
        UnusedSV: CryptographicSpongeVar<ConstraintF<G>, UnusedS>,
    >(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<UnusedSV>,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        if sponge.is_some() {
            unimplemented!(
                "ASForIpaPC is unable to accept sponge objects until IpaPC gets updated to accept them."
            );
        }

        let as_sponge =
            DomainSeparatedSpongeVar::<ConstraintF<G>, S, SV, ASForIpaPCDomain>::new(cs.clone());

        let mut verify_result = Boolean::TRUE;

        if new_accumulator_instance
            .ipa_commitment
            .shifted_comm
            .is_some()
        {
            return Ok(Boolean::FALSE);
        }

        let mut input_instances = input_instances.into_iter().collect::<Vec<_>>();
        let old_accumulator_instances = old_accumulator_instances.into_iter().collect::<Vec<_>>();

        let make_zk = proof.randomness.is_some();

        let default_input_instance;
        if !make_zk && input_instances.is_empty() && old_accumulator_instances.is_empty() {
            default_input_instance = Some(InputInstanceVar::new_constant(
                cs.clone(),
                InputInstance {
                    ipa_commitment: LabeledCommitment::new(
                        PolynomialLabel::new(),
                        ipa_pc::Commitment::default(),
                        None,
                    ),
                    point: G::ScalarField::zero(),
                    evaluation: G::ScalarField::zero(),
                    ipa_proof: verifier_key.default_proof.clone(),
                },
            )?);

            input_instances.push(default_input_instance.as_ref().unwrap())
        }

        // Step 2 of the scheme's common subroutine, as detailed in BCMS20.
        let succinct_check_result = Self::succinct_check_inputs(
            ns!(cs, "succinct_check_results").cs(),
            &verifier_key.ipa_svk,
            input_instances.into_iter().chain(old_accumulator_instances),
        )?;

        if let Some(randomness) = proof.randomness.as_ref() {
            let linear_polynomial_commitment = Self::deterministic_commit_to_linear_polynomial(
                &verifier_key.ipa_ck_linear,
                &randomness.random_linear_polynomial_coeffs,
            )?;

            verify_result = verify_result.and(
                &linear_polynomial_commitment
                    .is_eq(&randomness.random_linear_polynomial_commitment)?,
            )?;
        }

        // Steps 6-8 and 10 of the scheme's common subroutine, as detailed in BCMS20.
        let (
            combined_succinct_check_result,
            combined_commitment,
            randomized_combined_commitment,
            combined_check_poly_addends,
        ) = Self::combine_succinct_check_polynomials_and_commitments(
            &verifier_key.ipa_svk,
            &succinct_check_result,
            proof,
            as_sponge.clone(),
        )?;

        verify_result = verify_result.and(&combined_succinct_check_result)?;

        verify_result = verify_result.and(
            &randomized_combined_commitment.is_eq(&new_accumulator_instance.ipa_commitment.comm)?,
        )?;

        // Steps 9 of the scheme's common subroutine, as detailed in BCMS20.
        let challenge = Self::compute_new_challenge(
            as_sponge,
            &combined_commitment,
            &combined_check_poly_addends,
            proof
                .randomness
                .as_ref()
                .map(|r| &r.random_linear_polynomial_coeffs),
        )?;
        verify_result = verify_result.and(&challenge.is_eq(&new_accumulator_instance.point)?)?;

        // Steps outside of the common subroutine in the scheme's accumulation verifier, as detailed
        // in BCMS20.
        let eval = Self::evaluate_combined_check_polynomials(
            &combined_check_poly_addends,
            &challenge,
            proof
                .randomness
                .as_ref()
                .map(|r| &r.random_linear_polynomial_coeffs),
        )?;

        verify_result = verify_result.and(&eval.is_eq(&new_accumulator_instance.evaluation)?)?;

        Ok(verify_result)
    }
}

impl<G, C, S, SV> AtomicASVerifierGadget<ConstraintF<G>, AtomicASForInnerProductArgPC<G, S>>
    for AtomicASForIpaPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::tests::ASVerifierGadgetTests;
    use crate::ipa_pc_as::constraints::AtomicASForIpaPCVerifierGadget;
    use crate::ipa_pc_as::tests::{AtomicASForIpaPCTestInput, AtomicASForIpaPCTestParams};
    use crate::ipa_pc_as::AtomicASForInnerProductArgPC;
    use ark_relations::r1cs::SynthesisError;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = AtomicASForInnerProductArgPC<G, Sponge>;
    type I = AtomicASForIpaPCTestInput<CF, Sponge>;
    type ASV = AtomicASForIpaPCVerifierGadget<G, C, Sponge, SpongeVar>;

    type Tests = ASVerifierGadgetTests<CF, AS, ASV, I, Sponge, SpongeVar>;

    #[test]
    pub fn single_input_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }
}
