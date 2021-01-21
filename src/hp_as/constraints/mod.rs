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

mod data_structures;
pub use data_structures::*;

pub struct HPAccumulationSchemeGadget<G, C, S>
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

impl<G, C, S> HPAccumulationSchemeGadget<G, C, S> 
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
    S: CryptographicSpongeVar<ConstraintF<G>>,
{
    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a C>,
        challenges: &[Vec<Boolean<ConstraintF<G>>>],
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = C::zero();
        for (commitment, challenge) in commitments.into_iter().zip(challenges) {
            combined_commitment += &commitment.scalar_mul_le(challenge.iter())?;
        }

        Ok(combined_commitment)
    }

    fn compute_combined_hp_commitments(
        input_instances: &[&InputInstanceVar<G, C>],
        proof: &ProofVar<G, C>,
        mu_challenges: &[Vec<Boolean<ConstraintF<G>>>],
        nu_challenges: &[Vec<Boolean<ConstraintF<G>>>],
        combined_challenges: &[Vec<Boolean<ConstraintF<G>>>],
    ) -> Result<InputInstanceVar<G, C>, SynthesisError> {
        let num_inputs = input_instances.len();

        let comm_1 = Self::combine_commitments(
            input_instances.iter().map(|instance| &instance.comm_1),
            combined_challenges,
        )?;

        let comm_2 = Self::combine_commitments(
            input_instances
                .iter()
                .map(|instance| &instance.comm_2)
                .rev(),
            nu_challenges,
        )?;

        let comm_3 = {
            let t_comm_low_addend =
                Self::combine_commitments(proof.t_comms.0.iter(), &nu_challenges)?;
            let t_comm_high_addend =
                Self::combine_commitments(proof.t_comms.1.iter(), &nu_challenges[num_inputs..])?;

            let comm_3_addend = Self::combine_commitments(
                input_instances.iter().map(|instance| &instance.comm_3),
                &mu_challenges,
            )?
            .scalar_mul_le(nu_challenges[num_inputs - 1].iter())?;

            t_comm_low_addend + &t_comm_high_addend + &comm_3_addend
        };

        Ok(InputInstanceVar { 
            comm_1,
            comm_2,
            comm_3,
            _curve: PhantomData,
        })
    }

    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &VerifierKeyVar,
        input_instances: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        accumulator_instances: impl IntoIterator<Item = &'a InputInstanceVar<G, C>>,
        new_accumulator_instance: &InputInstanceVar<G, C>,
        proof: &ProofVar<G, C>,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self: 'a,
    {
        // TODO: Validate input instances
        let input_instances = input_instances
            .into_iter()
            .chain(accumulator_instances)
            .collect::<Vec<_>>();
        let num_inputs = input_instances.len();

        let mut challenges_sponge = S::new(cs.clone());
        // TODO: Absorb vk
        for input_instance in input_instances.iter() {
            input_instance.absorb_into_sponge(&mut challenges_sponge)?;
        }

        // TODO: Squeeze shorter bits
        // TODO: make the first element of `mu_challenges` be `1`, and skip
        // the scalar multiplication for it.
        let (mu_challenges_fe, mu_challenges_bits) =
            challenges_sponge.squeeze_nonnative_field_elements(num_inputs)?;

        proof.absorb_into_sponge(&mut challenges_sponge)?;

        let (mut nu_challenge_fe, _) = challenges_sponge.squeeze_nonnative_field_elements(1)?;
        let nu_challenge = nu_challenge_fe.pop().unwrap();
        let mut nu_challenges: Vec<NNFieldVar<G>> = Vec::with_capacity(2 * num_inputs - 1);
        let mut nu_challenges_bits: Vec<Vec<Boolean<ConstraintF<G>>>> = Vec::with_capacity(2 * num_inputs - 1);

        let mut cur_nu_challenge = NNFieldVar::<G>::one();
        for _ in 0..(2 * num_inputs - 1) {
            nu_challenges_bits.push(cur_nu_challenge.to_bits_le()?);
            nu_challenges.push(cur_nu_challenge.clone());
            cur_nu_challenge *= &nu_challenge;
        }

        let mut combined_challenges = Vec::with_capacity(num_inputs);
        for (mu, nu) in mu_challenges_fe.iter().zip(&nu_challenges) {
            combined_challenges.push((mu * nu).to_bits_le()?);
        }

        let accumulator_instance = Self::compute_combined_hp_commitments(
            input_instances.as_slice(),
            proof,
            &mu_challenges_bits,
            &nu_challenges_bits,
            combined_challenges.as_slice(),
        )?;
        let result1 = accumulator_instance.comm_1.is_eq(&new_accumulator_instance.comm_1)?;
        let result2 = accumulator_instance.comm_2.is_eq(&new_accumulator_instance.comm_2)?;
        let result3 = accumulator_instance.comm_3.is_eq(&new_accumulator_instance.comm_3)?;

        result1.and(&result2)?.and(&result3)
    }
}