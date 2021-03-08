use crate::constraints::{ASVerifierGadget, AtomicASVerifierGadget, ConstraintF, NNFieldVar};
use crate::ipa_as::{InnerProductArgAtomicAS, IpaPCDomain};
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
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget};
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::absorbable::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::domain_separated::constraints::DomainSeparatedSpongeVar;
use ark_sponge::domain_separated::DomainSeparatedSponge;
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use std::ops::Mul;

mod data_structures;
pub use data_structures::*;

pub struct IPAAtomicASVerifierGadget<G, C, S, SV>
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

impl<G, C, S, SV> IPAAtomicASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
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
        inputs
            .into_iter()
            .map(|input| {
                let ipa_commitment = &input.ipa_commitment;
                let (succinct_check_result, check_polynomial) = InnerProductArgPCGadget::<
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
        sponge: &mut SV,
        check_polynomial: &SuccinctCheckPolynomialVar<G>,
    ) -> Result<(), SynthesisError> {
        let mut bytes_input = Vec::new();
        for elem in &check_polynomial.0 {
            bytes_input.append(&mut elem.to_bytes()?);
        }

        sponge.absorb(&bytes_input)?;
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(ipa_vk, succinct_checks, proof, as_sponge))]
    fn combine_succinct_checks_and_proof<'a>(
        ipa_vk: &ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
        succinct_checks: &'a Vec<(
            Boolean<ConstraintF<G>>,
            SuccinctCheckPolynomialVar<G>,
            &FinalCommKeyVar<C>,
        )>,
        proof: &ProofVar<G, C>,
        as_sponge: SV,
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

            Self::absorb_check_polynomial_into_sponge(
                &mut linear_combination_challenge_sponge,
                check_polynomial,
            )?;

            linear_combination_challenge_sponge.absorb(&commitment)?;
        }

        let (linear_combination_challenges, linear_combination_challenge_bitss) =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); succinct_checks.len()].as_slice(),
            )?;

        let mut combined_commitment = if let Some(randomness) = proof.randomness.as_ref() {
            randomness.random_linear_polynomial_commitment.clone()
        } else {
            C::zero()
        };

        let mut combined_check_polynomial_and_addends = Vec::with_capacity(succinct_checks.len());
        let mut addend_bits = Vec::with_capacity(succinct_checks.len());

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

            addend_bits.push(cur_challenge_bits);
        }

        let randomized_combined_commitment = if let Some(randomness) = proof.randomness.as_ref() {
            ipa_vk
                .s
                .scalar_mul_le(randomness.commitment_randomness.iter())?
                + &combined_commitment
        } else {
            combined_commitment.clone()
        };

        let mut challenge_point_sponge = as_sponge;
        challenge_point_sponge.absorb(&combined_commitment)?;

        for ((_, check_polynomial), linear_combination_challenge_bits) in
            combined_check_polynomial_and_addends
                .iter()
                .zip(&addend_bits)
        {
            if log_supported_degree > (*check_polynomial).0.len() {
                combined_succinct_check_result = Boolean::FALSE;
                continue;
            }

            let linear_combination_challenge_bytes = linear_combination_challenge_bits
                .chunks(8)
                .map(UInt8::<ConstraintF<G>>::from_bits_le)
                .collect::<Vec<_>>();

            challenge_point_sponge.absorb(&linear_combination_challenge_bytes)?;

            Self::absorb_check_polynomial_into_sponge(
                &mut challenge_point_sponge,
                *check_polynomial,
            )?;
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])?
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
}

impl<G, C, S, SV> ASVerifierGadget<ConstraintF<G>, S, SV, InnerProductArgAtomicAS<G, S>>
    for IPAAtomicASVerifierGadget<G, C, S, SV>
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
            _verifier_key,
            _inputs,
            _old_accumulators,
            _new_accumulator,
            _proof,
            _sponge,
        )
    )]
    fn verify_with_sponge<'a>(
        _verifier_key: &Self::VerifierKey,
        _inputs: impl IntoIterator<Item = &'a Self::InputInstance>,
        _old_accumulators: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        _new_accumulator: &Self::AccumulatorInstance,
        _proof: &Self::Proof,
        _sponge: SV,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError> {
        unimplemented!(
            "IpaAS is unable to accept sponge objects until IpaPC gets updated to accept them too."
        );
    }

    #[tracing::instrument(
        target = "r1cs",
        skip(
            cs,
            verifier_key,
            inputs,
            old_accumulators,
            new_accumulator,
            proof,
        )
    )]
    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &Self::VerifierKey,
        inputs: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulators: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        let as_sponge = SV::new(cs.clone());

        let mut verify_result = Boolean::TRUE;

        if new_accumulator
            .ipa_commitment
            .shifted_comm
            .is_some()
        {
            return Ok(Boolean::FALSE);
        }

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

        // let cost = cs.num_constraints();
        let succinct_check_result = Self::succinct_check_inputs(
            ns!(cs, "succinct_check_results").cs(),
            &verifier_key.ipa_vk,
            inputs.into_iter().chain(old_accumulators),
        )?;

        let (
            combined_succinct_check_result,
            combined_commitment,
            combined_check_poly_addends,
            challenge,
        ) = Self::combine_succinct_checks_and_proof(
            &verifier_key.ipa_vk,
            &succinct_check_result,
            proof,
            as_sponge,
        )?;

        verify_result = verify_result.and(&combined_succinct_check_result)?;

        verify_result = verify_result
            .and(&combined_commitment.is_eq(&new_accumulator.ipa_commitment.comm)?)?;

        verify_result = verify_result.and(&challenge.is_eq(&new_accumulator.point)?)?;

        let mut eval =
            Self::evaluate_combined_check_polynomials(combined_check_poly_addends, &challenge)?;

        if let Some(randomness) = proof.randomness.as_ref() {
            eval += Self::evaluate_linear_polynomial(
                &randomness.random_linear_polynomial_coeffs,
                &challenge,
            );
        };

        verify_result = verify_result.and(&eval.is_eq(&new_accumulator.evaluation)?)?;

        Ok(verify_result)
    }
}

impl<G, C, S, SV> AtomicASVerifierGadget<ConstraintF<G>, S, SV, InnerProductArgAtomicAS<G, S>>
    for IPAAtomicASVerifierGadget<G, C, S, SV>
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
    use crate::ipa_as::constraints::IPAAtomicASVerifierGadget;
    use crate::ipa_as::tests::{IpaAtomicASTestInput, IpaAtomicASTestParams};
    use crate::ipa_as::InnerProductArgAtomicAS;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = InnerProductArgAtomicAS<G, Sponge>;
    type I = IpaAtomicASTestInput;
    type ASV = IPAAtomicASVerifierGadget<G, C, Sponge, SpongeVar>;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn test_initialization_no_zk() {
        Tests::test_initialization(
            &IpaAtomicASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_initialization_zk() {
        Tests::test_initialization(
            &IpaAtomicASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_no_zk() {
        Tests::test_simple_accumulation(
            &IpaAtomicASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_zk() {
        Tests::test_simple_accumulation(
            &IpaAtomicASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }
}
