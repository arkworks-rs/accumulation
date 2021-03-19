use crate::constraints::{ASVerifierGadget, NNFieldVar};
use crate::hp_as::data_structures::InputInstance;
use crate::hp_as::ASForHadamardProducts;
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::constraints::{bits_le_to_nonnative, CryptographicSpongeVar};
use ark_sponge::{absorb_gadget, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::vec;
use ark_std::vec::Vec;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`ASForHadamardProducts`][as_for_hp].
///
/// [as_for_hp]: crate::hp_as::ASForHadamardProducts
pub struct ASForHPVerifierGadget<G, C>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
    _curve: PhantomData<C>,
}

impl<G, C> ASForHPVerifierGadget<G, C>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    #[tracing::instrument(target = "r1cs", skip(sponge, num_inputs, make_zk))]
    fn squeeze_mu_challenges<S: CryptographicSponge<ConstraintF<G>>>(
        sponge: &mut impl CryptographicSpongeVar<ConstraintF<G>, S>,
        num_inputs: usize,
        make_zk: bool,
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

        if make_zk {
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

    #[tracing::instrument(target = "r1cs", skip(sponge, num_inputs))]
    fn squeeze_nu_challenges<S: CryptographicSponge<ConstraintF<G>>>(
        sponge: &mut impl CryptographicSpongeVar<ConstraintF<G>, S>,
        num_inputs: usize,
    ) -> Result<Vec<Vec<Boolean<ConstraintF<G>>>>, SynthesisError> {
        let nu_size = FieldElementSize::Truncated(128);
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

    #[tracing::instrument(
        target = "r1cs",
        skip(commitments, challenges, extra_challenges, hiding_comms)
    )]
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

    #[tracing::instrument(
        target = "r1cs",
        skip(input_instances, proof, mu_challenges, nu_challenges)
    )]
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

    fn check_verify_inputs(inputs: &Vec<&InputInstanceVar<G, C>>, proof: &ProofVar<G, C>) -> bool {
        let num_inputs = inputs.len();
        if num_inputs == 0 {
            return false;
        }

        if proof.t_comms.low.len() != proof.t_comms.high.len() {
            return false;
        }

        let placeholder_input = if proof.hiding_comms.is_some() && num_inputs == 1 {
            1
        } else {
            0
        };

        if proof.t_comms.low.len() != num_inputs - 1 + placeholder_input {
            return false;
        }

        true
    }
}

impl<G, C> ASVerifierGadget<ConstraintF<G>, ASForHadamardProducts<G>>
    for ASForHPVerifierGadget<G, C>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
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
            sponge
        )
    )]
    fn verify<
        'a,
        S: CryptographicSponge<ConstraintF<G>>,
        SV: CryptographicSpongeVar<ConstraintF<G>, S>,
    >(
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
        let sponge = sponge.unwrap_or_else(|| SV::new(cs));

        let mut input_instances = input_instances
            .into_iter()
            .chain(old_accumulator_instances)
            .collect::<Vec<_>>();

        if !Self::check_verify_inputs(&input_instances, proof) {
            return Ok(Boolean::FALSE);
        }

        let mut num_inputs = input_instances.len();
        let make_zk = proof.hiding_comms.is_some();

        let default_input_instance;
        if make_zk && num_inputs == 1 {
            default_input_instance = Some(InputInstanceVar::new_constant(
                sponge.cs(),
                InputInstance::default(),
            )?);

            num_inputs += 1;
            input_instances.push(default_input_instance.as_ref().unwrap());
        };

        let mut challenges_sponge = sponge;
        absorb_gadget!(
            &mut challenges_sponge,
            &verifier_key.num_supported_elems,
            &input_instances,
            &proof.hiding_comms
        );

        let mu_challenges_bits =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_inputs, make_zk)?;

        challenges_sponge.absorb(&proof.t_comms)?;

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
    use crate::constraints::tests::ASVerifierGadgetTests;
    use crate::hp_as::constraints::ASForHPVerifierGadget;
    use crate::hp_as::tests::{ASForHPTestInput, ASForHPTestParams};
    use crate::hp_as::ASForHadamardProducts;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = ASForHadamardProducts<G>;
    type I = ASForHPTestInput;
    type ASV = ASForHPVerifierGadget<G, C>;

    type Tests = ASVerifierGadgetTests<CF, AS, ASV, I, Sponge, SpongeVar>;

    #[test]
    pub fn test_initialization_no_zk() {
        Tests::test_initialization(
            &ASForHPTestParams {
                vector_len: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_initialization_zk() {
        Tests::test_initialization(
            &ASForHPTestParams {
                vector_len: 8,
                make_zk: true,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_no_zk() {
        Tests::test_simple_accumulation(
            &ASForHPTestParams {
                vector_len: 8,
                make_zk: false,
            },
            1,
        );
    }

    #[test]
    pub fn test_simple_accumulation_zk() {
        Tests::test_simple_accumulation(
            &ASForHPTestParams {
                vector_len: 8,
                make_zk: true,
            },
            1,
        );
    }
}
