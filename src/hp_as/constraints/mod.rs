use crate::constraints::{AidedAccumulationSchemeVerifierGadget, ConstraintF, NNFieldVar};
use ark_ec::AffineCurve;
use ark_ff::{Field, ToConstraintField};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{R1CSVar, ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use std::marker::PhantomData;

mod data_structures;
use crate::hp_as::HPAidedAccumulationScheme;
use crate::AidedAccumulationScheme;
use ark_sponge::{Absorbable, CryptographicSponge};
pub use data_structures::*;
use crate::hp_as::data_structures::InputInstance;
use ark_r1cs_std::alloc::AllocVar;

pub struct HPAidedAccumulationSchemeVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    pub _affine: PhantomData<G>,
    pub _curve: PhantomData<C>,
    pub _sponge: PhantomData<SV>,
}

impl<G, C, SV> HPAidedAccumulationSchemeVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a C>,
        challenges: &[Vec<Boolean<ConstraintF<G>>>],
        hiding_comms: Option<&C>,
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = C::zero();
        for (commitment, challenge) in commitments.into_iter().zip(challenges) {
            combined_commitment += &commitment.scalar_mul_le(challenge.iter())?;
        }

        if let Some(hiding_comms) = hiding_comms {
            combined_commitment += hiding_comms;
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

        let hiding_comm_addend_1 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| {
                hiding_comms
                    .comm_1
                    .scalar_mul_le(mu_challenges[num_inputs].iter())
            })
            .transpose()?;

        let comm_1 = Self::combine_commitments(
            input_instances.iter().map(|instance| &instance.comm_1),
            combined_challenges,
            hiding_comm_addend_1.as_ref(),
        )?;

        let hiding_comm_addend_2 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| hiding_comms.comm_2.scalar_mul_le(mu_challenges[1].iter()))
            .transpose()?;

        let comm_2 = Self::combine_commitments(
            input_instances
                .iter()
                .map(|instance| &instance.comm_2)
                .rev(),
            nu_challenges,
            hiding_comm_addend_2.as_ref(),
        )?;

        let comm_3 = {
            let t_comm_low_addend =
                Self::combine_commitments(proof.t_comms.low.iter(), &nu_challenges, None)?;
            let t_comm_high_addend = Self::combine_commitments(
                proof.t_comms.high.iter(),
                &nu_challenges[num_inputs..],
                None,
            )?;

            let hiding_comm_addend_3 = proof
                .hiding_comms
                .as_ref()
                .map(|hiding_comms| {
                    hiding_comms
                        .comm_3
                        .scalar_mul_le(mu_challenges[num_inputs].iter())
                })
                .transpose()?;

            let comm_3_addend = Self::combine_commitments(
                input_instances.iter().map(|instance| &instance.comm_3),
                &mu_challenges,
                hiding_comm_addend_3.as_ref(),
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
}

impl<G, S, C, SV>
    AidedAccumulationSchemeVerifierGadget<
        HPAidedAccumulationScheme<G, ConstraintF<G>, S>,
        ConstraintF<G>,
    > for HPAidedAccumulationSchemeVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    type VerifierKey = VerifierKeyVar<ConstraintF<G>>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = AccumulatorInstanceVar<G, C>;
    type Proof = ProofVar<G, C>;

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
        // TODO: Validate input instances
        let mut input_instances = input_instances
            .into_iter()
            .chain(accumulator_instances)
            .collect::<Vec<_>>();

        let mut num_inputs = input_instances.len();
        let has_hiding = proof.hiding_comms.is_some();

        let mut default_input_instance = None;
        if has_hiding && num_inputs == 1 {
            default_input_instance = Some(InputInstanceVar::new_constant(cs.clone(), InputInstance::default())?);

            num_inputs += 1;
            input_instances.push(default_input_instance.as_ref().unwrap());
        };

        let mut challenges_sponge = SV::new(cs.clone());
        challenges_sponge.absorb(&[verifier_key.num_supported_elems.clone()]);
        for input_instance in input_instances.iter() {
            input_instance.absorb_into_sponge(&mut challenges_sponge)?;
        }

        challenges_sponge
            .absorb(&[FpVar::from(Boolean::constant(proof.hiding_comms.is_some()))])?;
        if let Some(t_comms) = proof.hiding_comms.as_ref() {
            t_comms.absorb_into_sponge(&mut challenges_sponge)?;
        }

        // TODO: Squeeze shorter bits
        // TODO: make the first element of `mu_challenges` be `1`, and skip
        // the scalar multiplication for it.
        let (mut mu_challenges_fe, mut mu_challenges_bits) =
            challenges_sponge.squeeze_nonnative_field_elements(num_inputs)?;
        if has_hiding {
            mu_challenges_fe.push(mu_challenges_fe[1].clone() * &mu_challenges_fe[num_inputs - 1]);
            mu_challenges_bits.push(mu_challenges_fe.last().unwrap().to_bits_le()?);
        }

        proof.t_comms.absorb_into_sponge(&mut challenges_sponge)?;

        let (mut nu_challenge_fe, _) = challenges_sponge.squeeze_nonnative_field_elements(1)?;
        let nu_challenge = nu_challenge_fe.pop().unwrap();
        let mut nu_challenges: Vec<NNFieldVar<G>> = Vec::with_capacity(2 * num_inputs - 1);
        let mut nu_challenges_bits: Vec<Vec<Boolean<ConstraintF<G>>>> =
            Vec::with_capacity(2 * num_inputs - 1);

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

        let result1 = accumulator_instance
            .comm_1
            .is_eq(&new_accumulator_instance.comm_1)?;
        let result2 = accumulator_instance
            .comm_2
            .is_eq(&new_accumulator_instance.comm_2)?;
        let result3 = accumulator_instance
            .comm_3
            .is_eq(&new_accumulator_instance.comm_3)?;

        result1.and(&result2)?.and(&result3)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::hp_as::constraints::HPAidedAccumulationSchemeVerifierGadget;
    use crate::hp_as::tests::HPAidedAccumulationSchemeTestInput;
    use crate::hp_as::HPAidedAccumulationScheme;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    //type G = ark_pallas::Affine;
    //type C = ark_pallas::constraints::GVar;
    //type F = ark_pallas::Fr;
    //type ConstraintF = ark_pallas::Fq;
    type G = ark_ed_on_bls12_381::EdwardsAffine;
    type C = ark_ed_on_bls12_381::constraints::EdwardsVar;
    type F = ark_ed_on_bls12_381::Fr;
    type ConstraintF = ark_ed_on_bls12_381::Fq;

    type Sponge = PoseidonSponge<ConstraintF>;
    type SpongeVar = PoseidonSpongeVar<ConstraintF>;

    type AS = HPAidedAccumulationScheme<G, ConstraintF, Sponge>;
    type I = HPAidedAccumulationSchemeTestInput;
    type ASV = HPAidedAccumulationSchemeVerifierGadget<G, C, SpongeVar>;

    #[test]
    pub fn basic_test() {
        crate::constraints::tests::basic_test::<AS, I, ConstraintF, ASV>(&(8, true), 20);
    }
}
