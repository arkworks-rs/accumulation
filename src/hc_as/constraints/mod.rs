use crate::constraints::{ASVerifierGadget, ConstraintF, NNFieldVar};
use crate::hc_as::HomomorphicCommitmentAS;
use ark_ec::AffineCurve;
use ark_ff::{Field, ToConstraintField};
use ark_nonnative_field::NonNativeFieldMulResultVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::constraints::absorbable::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::ops::Mul;
use std::marker::PhantomData;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`HomomorphicCommitmentAS`][hc_as].
///
/// [hc_as]: crate::hc_as::HomomorphicCommitmentAS
pub struct HcASVerifierGadget<G, C, S, SV>
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

impl<G, C, S, SV> HcASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
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

    fn basic_verify(
        input_instances: &Vec<&InputInstanceVar<G, C>>,
        proof: &ProofVar<G, C>,
    ) -> bool {
        if input_instances.len() != proof.single_proofs.len() {
            return false;
        }

        true
    }
}

impl<G, C, S, SV> ASVerifierGadget<ConstraintF<G>, S, SV, HomomorphicCommitmentAS<G, S>>
    for HcASVerifierGadget<G, C, S, SV>
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
    fn verify_with_sponge<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: SV,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        let input_instances = input_instances
            .into_iter()
            .chain(old_accumulator_instances)
            .collect::<Vec<_>>();

        if !Self::basic_verify(&input_instances, proof) {
            return Ok(Boolean::FALSE);
        }

        let mut verify_result = Boolean::TRUE;

        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(&verifier_key.0)?;

        let mut commitment = Vec::new();
        for (input_instance, single_proof) in input_instances
            .into_iter()
            .zip(&proof.single_proofs)
        {
            absorb_gadget!(
                &mut challenge_point_sponge,
                input_instance,
                single_proof.witness_commitment
            );

            let eval_check_lhs: NNFieldVar<G> = &single_proof.eval - &input_instance.eval;
            let eval_check_rhs: NNFieldVar<G> = (&single_proof.witness_eval)
                .mul(&(&new_accumulator_instance.point - &input_instance.point));

            let eval_check = eval_check_lhs.is_eq(&eval_check_rhs)?;
            verify_result = verify_result.and(&eval_check)?;

            commitment.push(&input_instance.commitment);
        }

        let mut challenge_point_sponge_field_element_and_bits = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])?;

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

        let mut linear_combination_challenge_sponge = sponge;

        let challenge_point_bytes = challenge_point_bits
            .chunks(8)
            .map(UInt8::<ConstraintF<G>>::from_bits_le)
            .collect::<Vec<_>>();

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
                vec![FieldElementSize::Truncated(128); proof.single_proofs.len() * 2].as_slice(),
            )?;

        let combined_eval = Self::combine_evaluation(
            proof
                .single_proofs
                .iter()
                .map(|p| &p.eval)
                .chain(proof.single_proofs.iter().map(|p| &p.witness_eval)),
            linear_combination_challenge.as_slice(),
        )?;

        verify_result = verify_result.and(&combined_eval.is_eq(&new_accumulator_instance.eval)?)?;

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
    use crate::hc_as::constraints::HcASVerifierGadget;
    use crate::hc_as::tests::{HcASTestInput, HcASTestParams};
    use crate::hc_as::HomomorphicCommitmentAS;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = HomomorphicCommitmentAS<G, Sponge>;
    type ASV = HcASVerifierGadget<G, C, Sponge, SpongeVar>;
    type I = HcASTestInput;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn test_initialization_no_zk() {
        Tests::test_initialization(
            &HcASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_initialization_zk() {
        Tests::test_initialization(
            &HcASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_no_zk() {
        Tests::test_simple_accumulation(
            &HcASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_zk() {
        Tests::test_simple_accumulation(
            &HcASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn print_breakdown() {
        Tests::print_costs_breakdown(&HcASTestParams {
            degree: 8,
            make_zk: true,
        });
    }
}
