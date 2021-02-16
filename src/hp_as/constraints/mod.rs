use crate::constraints::{ConstraintF, NNFieldVar, SplitASVerifierGadget};
use crate::hp_as::data_structures::InputInstance;
use crate::hp_as::HPSplitAS;
use ark_ec::AffineCurve;
use ark_ff::ToConstraintField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{R1CSVar, ToBitsGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{bits_le_to_nonnative, CryptographicSpongeVar};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use std::marker::PhantomData;
use std::ops::Mul;

pub mod data_structures;
use data_structures::*;

pub struct HPSplitASVerifierGadget<G, C, SV>
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

impl<G, C, SV> HPSplitASVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    fn squeeze_mu_challenges(
        sponge: &mut SV,
        num_inputs: usize,
        has_hiding: bool,
    ) -> Result<Vec<Vec<Boolean<ConstraintF<G>>>>, SynthesisError> {
        let mut mu_challenges_bits = Vec::with_capacity(num_inputs);
        mu_challenges_bits.push(vec![Boolean::TRUE]);

        if num_inputs > 1 {
            let mu_challenges_bits_rest = sponge.squeeze_bits(128 * (num_inputs - 1))?;
            mu_challenges_bits_rest
                .chunks(128)
                .into_iter()
                .for_each(|bits| mu_challenges_bits.push(bits.to_vec()));
        }

        if has_hiding {
            let hiding_components_bits =
                vec![&mu_challenges_bits[1], &mu_challenges_bits[num_inputs - 1]];
            let mut hiding_components_fe: Vec<NNFieldVar<G>> =
                bits_le_to_nonnative(sponge.cs().clone(), hiding_components_bits)?;
            mu_challenges_bits.push(
                (hiding_components_fe
                    .pop()
                    .unwrap()
                    .mul(&hiding_components_fe.pop().unwrap()))
                .to_bits_le()?,
            );
        }

        Ok(mu_challenges_bits)
    }

    fn squeeze_nu_challenges(
        sponge: &mut SV,
        num_inputs: usize,
    ) -> Result<Vec<Vec<Boolean<ConstraintF<G>>>>, SynthesisError> {
        let nu_size = FieldElementSize::Truncated { num_bits: 128 };
        let (mut nu_challenge_fe, mut nu_challenge_bits) =
            sponge.squeeze_nonnative_field_elements_with_sizes(vec![nu_size].as_slice())?;
        let nu_challenge_fe: NNFieldVar<G> = nu_challenge_fe.pop().unwrap();

        let mut nu_challenges_bits: Vec<Vec<Boolean<ConstraintF<G>>>> =
            Vec::with_capacity(2 * num_inputs - 1);

        nu_challenges_bits.push(vec![Boolean::TRUE]);
        nu_challenges_bits.push(nu_challenge_bits.pop().unwrap());

        let mut cur_nu_challenge = nu_challenge_fe.clone();
        for _ in 2..(num_inputs + 1) {
            cur_nu_challenge *= &nu_challenge_fe;
            nu_challenges_bits.push(cur_nu_challenge.to_bits_le()?);
        }

        Ok(nu_challenges_bits)
    }

    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a C>,
        challenges: &[Vec<Boolean<ConstraintF<G>>>],
        extra_challenges: Option<&[Vec<Boolean<ConstraintF<G>>>]>,
        hiding_comms: Option<&C>,
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = hiding_comms.map(C::clone).unwrap_or(C::zero());
        for (i, commitment) in commitments.into_iter().enumerate() {
            let mut addend = commitment.clone();
            if !(challenges[i].len() == 1 && challenges[i][0].eq(&Boolean::TRUE)) {
                addend = addend.scalar_mul_le(challenges[i].iter())?;
            }

            if let Some(extra_challenge) =
                extra_challenges.as_ref().map(|challenges| &challenges[i])
            {
                if !(extra_challenge.len() == 1 && extra_challenge[0].eq(&Boolean::TRUE)) {
                    addend = addend.scalar_mul_le(extra_challenge.iter())?;
                }
            }

            combined_commitment += &addend;
        }

        Ok(combined_commitment)
    }

    fn compute_combined_hp_commitments(
        input_instances: &[&InputInstanceVar<G, C>],
        proof: &ProofVar<G, C>,
        mu_challenges: &[Vec<Boolean<ConstraintF<G>>>],
        nu_challenges: &[Vec<Boolean<ConstraintF<G>>>],
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
            mu_challenges,
            Some(nu_challenges),
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
            None,
            hiding_comm_addend_2.as_ref(),
        )?;

        let comm_3 = {
            let t_comm_low_addend =
                Self::combine_commitments(proof.t_comms.low.iter(), &nu_challenges, None, None)?;

            let t_comm_high_addend =
                Self::combine_commitments(proof.t_comms.high.iter(), &nu_challenges, None, None)?
                    .scalar_mul_le(nu_challenges[1].iter())?;

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
                None,
                hiding_comm_addend_3.as_ref(),
            )?;

            t_comm_low_addend
                + &(t_comm_high_addend + &comm_3_addend)
                    .scalar_mul_le(nu_challenges[num_inputs - 1].iter())?
        };

        Ok(InputInstanceVar {
            comm_1,
            comm_2,
            comm_3,
            _curve: PhantomData,
        })
    }
}

impl<G, S, C, SV> SplitASVerifierGadget<HPSplitAS<G, S>, ConstraintF<G>>
    for HPSplitASVerifierGadget<G, C, SV>
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
            default_input_instance = Some(InputInstanceVar::new_constant(
                cs.clone(),
                InputInstance::default(),
            )?);

            num_inputs += 1;
            input_instances.push(default_input_instance.as_ref().unwrap());
        };

        let mut challenges_sponge = SV::new(cs.clone());
        challenges_sponge.absorb(&[verifier_key.num_supported_elems.clone()])?;
        for input_instance in input_instances.iter() {
            input_instance.absorb_into_sponge(&mut challenges_sponge)?;
        }

        challenges_sponge
            .absorb(&[FpVar::from(Boolean::constant(proof.hiding_comms.is_some()))])?;
        if let Some(t_comms) = proof.hiding_comms.as_ref() {
            t_comms.absorb_into_sponge(&mut challenges_sponge)?;
        }

        let mu_challenges_bits =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_inputs, has_hiding)?;

        proof.t_comms.absorb_into_sponge(&mut challenges_sponge)?;

        let nu_challenges_bits = Self::squeeze_nu_challenges(&mut challenges_sponge, num_inputs)?;

        let accumulator_instance = Self::compute_combined_hp_commitments(
            input_instances.as_slice(),
            proof,
            &mu_challenges_bits,
            &nu_challenges_bits,
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
    use crate::hp_as::constraints::HPSplitASVerifierGadget;
    use crate::hp_as::tests::HPSplitASTestInput;
    use crate::hp_as::HPSplitAS;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type F = ark_pallas::Fr;
    type ConstraintF = ark_pallas::Fq;
    /*
    type G = ark_ed_on_bls12_381::EdwardsAffine;
    type C = ark_ed_on_bls12_381::constraints::EdwardsVar;
    type F = ark_ed_on_bls12_381::Fr;
    type ConstraintF = ark_ed_on_bls12_381::Fq;

     */

    type Sponge = PoseidonSponge<ConstraintF>;
    type SpongeVar = PoseidonSpongeVar<ConstraintF>;

    type AS = HPSplitAS<G, Sponge>;
    type I = HPSplitASTestInput;
    type ASV = HPSplitASVerifierGadget<G, C, SpongeVar>;

    #[test]
    pub fn basic_test() {
        crate::constraints::tests::print_breakdown::<AS, I, ConstraintF, ASV>(&(1, false));
    }

    #[test]
    pub fn basic_test_hiding() {
        crate::constraints::tests::print_breakdown::<AS, I, ConstraintF, ASV>(&(1, true));
    }
}
