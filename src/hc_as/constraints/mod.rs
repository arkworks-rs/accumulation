use crate::constraints::{ASVerifierGadget, ConstraintF, NNFieldVar};
use crate::hc_as::HomomorphicCommitmentAS;
use crate::AccumulationScheme;
use ark_ec::AffineCurve;
use ark_ff::{Field, ToConstraintField};
use ark_nonnative_field::NonNativeFieldMulResultVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::ops::Mul;
use data_structures::*;
use std::marker::PhantomData;

pub mod data_structures;

pub struct HcASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
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

impl<G, C, S, SV> HcASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
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
}

impl<G, C, S, SV> ASVerifierGadget<HomomorphicCommitmentAS<G, S>, ConstraintF<G>>
    for HcASVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
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
        let mut verify_result = Boolean::TRUE;

        let mut challenge_point_sponge = SV::new(cs.clone());
        challenge_point_sponge.absorb(&[verifier_key.0.clone()])?;

        let mut commitment = Vec::new();
        for (input_instance, single_proof) in input_instances
            .into_iter()
            .chain(accumulator_instances)
            .zip(&proof.single_proofs)
        {
            input_instance.absorb_into_sponge::<S, SV>(&mut challenge_point_sponge)?;
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

        let mut linear_combination_challenge_sponge = SV::new(cs.clone());

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

        for single_proof in &proof.single_proofs {
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
                vec![FieldElementSize::Truncated { num_bits: 128 }; proof.single_proofs.len() * 2]
                    .as_slice(),
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
    use crate::hc_as::constraints::{
        HcASVerifierGadget, InputInstanceVar, ProofVar, VerifierKeyVar,
    };
    use crate::hc_as::tests::{HcASTestInput, HcASTestParams};
    use crate::hc_as::HomomorphicCommitmentAS;
    use crate::tests::ASTestInput;
    use crate::AccumulationScheme;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_std::test_rng;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<ConstraintF>;
    type SpongeVar = PoseidonSpongeVar<ConstraintF>;

    type AS = HomomorphicCommitmentAS<G, Sponge>;
    type I = HcASTestInput;
    type ASV = HcASVerifierGadget<G, C, Sponge, SpongeVar>;

    #[test]
    pub fn test_initialization_no_zk() {
        crate::constraints::tests::test_initialization::<AS, I, ConstraintF, ASV>(
            &HcASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_initialization_zk() {
        crate::constraints::tests::test_initialization::<AS, I, ConstraintF, ASV>(
            &HcASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_no_zk() {
        crate::constraints::tests::test_simple_accumulation::<AS, I, ConstraintF, ASV>(
            &HcASTestParams {
                degree: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_zk() {
        crate::constraints::tests::test_simple_accumulation::<AS, I, ConstraintF, ASV>(
            &HcASTestParams {
                degree: 8,
                make_zk: true,
            },
            1,
        );
    }
}
