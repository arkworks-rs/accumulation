use crate::constraints::ASVerifierGadget;
use crate::trivial_pc_as::{
    ASForTrivialPC, InputInstance, CHALLENGE_POINT_SIZE, LINEAR_COMBINATION_CHALLENGE_SIZE,
};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::{Field, ToConstraintField};
use ark_nonnative_field::{NonNativeFieldMulResultVar, NonNativeFieldVar};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::vec;
use ark_std::vec::Vec;
use std::ops::Mul;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`ASForTrivialPC`][as_for_trivial_pc].
///
/// [as_for_trivial_pc]: crate::trivial_pc_as::ASForTrivialPC
pub struct ASForTrivialPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
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

impl<G, C, S, SV> ASForTrivialPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    /// Check that the proof is properly structured.
    fn check_proof_structure(proof: &ProofVar<G, C>, num_inputs: usize) -> bool {
        // Each proof must correspond to an input.
        return proof.single_proofs.len() == num_inputs;
    }

    /// Compute the linear combination of evaluations.
    #[tracing::instrument(target = "r1cs", skip(evaluations, challenge))]
    fn combine_evaluation<'a>(
        evaluations: impl IntoIterator<Item = &'a NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,
        challenge: &[NonNativeFieldVar<G::ScalarField, ConstraintF<G>>],
    ) -> Result<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>, SynthesisError> {
        let mut combined_evaluation =
            NonNativeFieldMulResultVar::<G::ScalarField, ConstraintF<G>>::zero();
        for (i, eval) in evaluations.into_iter().enumerate() {
            combined_evaluation += (&eval).mul_without_reduce(&challenge[i])?;
        }

        Ok(combined_evaluation.reduce()?)
    }

    /// Compute the linear combination of commitments.
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
}

impl<G, C, S, SV> ASVerifierGadget<ConstraintF<G>, S, SV, ASForTrivialPC<G, S>>
    for ASForTrivialPCVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    type VerifierKey = VerifierKeyVar<ConstraintF<G>>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = InputInstanceVar<G, C>;
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

        let mut all_input_instances = input_instances
            .into_iter()
            .chain(old_accumulator_instances)
            .collect::<Vec<_>>();

        let default_input_instance;
        if all_input_instances.is_empty() {
            default_input_instance = Some(InputInstanceVar::new_constant(
                cs,
                InputInstance::placeholder(),
            )?);
            all_input_instances.push(default_input_instance.as_ref().unwrap());
        }

        if !Self::check_proof_structure(proof, all_input_instances.len()) {
            return Ok(Boolean::FALSE);
        }

        let mut verify_result = Boolean::TRUE;

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(&verifier_key.0)?;

        let mut commitment = Vec::new();
        for (input_instance, single_proof) in
            all_input_instances.into_iter().zip(&proof.single_proofs)
        {
            // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
            absorb_gadget!(
                &mut challenge_point_sponge,
                input_instance,
                single_proof.witness_commitment
            );

            // Step 4 of the scheme's accumulation verifier, as detailed in BCLMS20.
            let eval_check_lhs: NonNativeFieldVar<G::ScalarField, ConstraintF<G>> =
                &single_proof.eval - &input_instance.eval;
            let eval_check_rhs: NonNativeFieldVar<G::ScalarField, ConstraintF<G>> = (&single_proof
                .witness_eval)
                .mul(&(&new_accumulator_instance.point - &input_instance.point));

            let eval_check = eval_check_lhs.is_eq(&eval_check_rhs)?;
            verify_result = verify_result.and(&eval_check)?;

            commitment.push(&input_instance.commitment);
        }

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut challenge_point_sponge_field_element_and_bits = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(
                CHALLENGE_POINT_SIZE,
            )])?;

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

        // Step 5 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut linear_combination_challenge_sponge = sponge;
        let challenge_point_bytes = challenge_point_bits
            .chunks(8)
            .map(|bits| {
                if bits.len() == 8 {
                    UInt8::<ConstraintF<G>>::from_bits_le(bits)
                } else {
                    let mut bits_tmp = bits.to_vec();
                    bits_tmp.resize_with(8, || Boolean::FALSE);
                    UInt8::<ConstraintF<G>>::from_bits_le(bits_tmp.as_slice())
                }
            })
            .collect::<Vec<_>>();

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        linear_combination_challenge_sponge.absorb(&challenge_point_bytes)?;

        for single_proof in &proof.single_proofs {
            absorb_gadget!(
                &mut linear_combination_challenge_sponge,
                single_proof.eval.to_bytes()?,
                single_proof.witness_eval.to_bytes()?
            );
        }

        let (linear_combination_challenge, linear_combination_challenge_bits) =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![
                    FieldElementSize::Truncated(LINEAR_COMBINATION_CHALLENGE_SIZE);
                    proof.single_proofs.len() * 2
                ]
                .as_slice(),
            )?;

        // Step 6 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let combined_eval = Self::combine_evaluation(
            proof
                .single_proofs
                .iter()
                .map(|p| &p.eval)
                .chain(proof.single_proofs.iter().map(|p| &p.witness_eval)),
            linear_combination_challenge.as_slice(),
        )?;

        verify_result = verify_result.and(&combined_eval.is_eq(&new_accumulator_instance.eval)?)?;

        // Step 7 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let combined_commitment = Self::combine_commitment(
            commitment
                .into_iter()
                .chain(proof.single_proofs.iter().map(|p| &p.witness_commitment)),
            linear_combination_challenge_bits.as_slice(),
        )?;

        verify_result =
            verify_result.and(&combined_commitment.is_eq(&new_accumulator_instance.commitment)?)?;

        Ok(verify_result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::tests::ASVerifierGadgetTests;
    use crate::trivial_pc_as::constraints::ASForTrivialPCVerifierGadget;
    use crate::trivial_pc_as::tests::{ASForTrivialPCTestInput, ASForTrivialPCTestParams};
    use crate::trivial_pc_as::ASForTrivialPC;
    use ark_relations::r1cs::SynthesisError;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = ASForTrivialPC<G, Sponge>;
    type ASV = ASForTrivialPCVerifierGadget<G, C, Sponge, SpongeVar>;
    type I = ASForTrivialPCTestInput;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn single_input_init_test() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn multiple_inputs_init_test() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn simple_accumulation_test() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn accumulators_only_test() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn no_inputs_init_test() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }
}
