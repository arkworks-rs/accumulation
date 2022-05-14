use crate::constraints::ASVerifierGadget;
use crate::hp_as::data_structures::InputInstance;
use crate::hp_as::{ASForHadamardProducts, CHALLENGE_SIZE};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{R1CSVar, ToBitsGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::constraints::{bits_le_to_nonnative, CryptographicSpongeVar};
use ark_sponge::{absorb_gadget, Absorb, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::vec;
use ark_std::vec::Vec;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`ASForHadamardProducts`][as_for_hp].
///
/// [as_for_hp]: crate::hp_as::ASForHadamardProducts
pub struct ASForHPVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    _affine: PhantomData<G>,
    _curve: PhantomData<C>,
    _sponge: PhantomData<S>,
    _sponge_var: PhantomData<SV>,
}

impl<G, C, S, SV> ASForHPVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<ConstraintF<G>, S>,
{
    /// Check that the input witness is properly structured.
    fn check_proof_structure(proof: &ProofVar<G, C>, num_inputs: usize) -> bool {
        assert!(num_inputs > 0);

        // The number of commitments to the low and high coefficients must be equal, given how
        // they were computed.
        if proof.product_poly_comm.low.len() != proof.product_poly_comm.high.len() {
            return false;
        }

        // The number of commitments can be derived from the number of inputs. Ensure that
        // they match.
        if proof.product_poly_comm.low.len() != num_inputs - 1 {
            return false;
        }

        true
    }

    /// Compute the mu challenges from a provided sponge.
    #[tracing::instrument(target = "r1cs", skip(sponge, num_inputs, make_zk))]
    fn squeeze_mu_challenges(
        sponge: &mut impl CryptographicSpongeVar<ConstraintF<G>, S>,
        num_inputs: usize,
        make_zk: bool,
    ) -> Result<Vec<Vec<Boolean<ConstraintF<G>>>>, SynthesisError> {
        let mut mu_challenges_bits = Vec::with_capacity(num_inputs);
        mu_challenges_bits.push(vec![Boolean::<ConstraintF<G>>::TRUE]);

        if num_inputs > 1 {
            let mu_size = FieldElementSize::Truncated(CHALLENGE_SIZE);
            let (_, mu_challenge_bits_rem) = sponge
                .squeeze_nonnative_field_elements_with_sizes::<G::ScalarField>(
                    vec![mu_size; num_inputs - 1].as_slice(),
                )?;
            mu_challenges_bits.extend(mu_challenge_bits_rem);
        }

        if make_zk {
            let hiding_components_bits =
                vec![&mu_challenges_bits[1], &mu_challenges_bits[num_inputs - 1]];
            let mut hiding_components_fe: Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>> =
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

    /// Compute the nu challenges from a provided sponge.
    #[tracing::instrument(target = "r1cs", skip(sponge, num_inputs))]
    fn squeeze_nu_challenges(
        sponge: &mut impl CryptographicSpongeVar<ConstraintF<G>, S>,
        num_inputs: usize,
    ) -> Result<Vec<Vec<Boolean<ConstraintF<G>>>>, SynthesisError> {
        let nu_size = FieldElementSize::Truncated(CHALLENGE_SIZE);
        let (mut nu_challenge_fe, mut nu_challenge_bits) =
            sponge.squeeze_nonnative_field_elements_with_sizes(vec![nu_size].as_slice())?;
        let nu_challenge_fe: NonNativeFieldVar<G::ScalarField, ConstraintF<G>> =
            nu_challenge_fe.pop().unwrap();

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

    /// Computes the linear combination of Pedersen commitments.
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

    /// Combines the accumulation input instances into a single input instance.
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
            let product_poly_comm_low_addend = Self::combine_commitments(
                proof.product_poly_comm.low.iter(),
                &nu_challenges,
                None,
                None,
            )?;

            let product_poly_comm_high_addend = Self::combine_commitments(
                proof.product_poly_comm.high.iter(),
                &nu_challenges,
                None,
                None,
            )?
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

            product_poly_comm_low_addend
                + &(product_poly_comm_high_addend + &comm_3_addend)
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

impl<G, C, S, SV> ASVerifierGadget<ConstraintF<G>, S, SV, ASForHadamardProducts<G, S>>
    for ASForHPVerifierGadget<G, C, S, SV>
where
    G: AffineCurve + Absorb,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
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
            sponge
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
        assert!(!sponge.is_none());
        let sponge = sponge.unwrap();

        let mut input_instances = input_instances.into_iter().collect::<Vec<_>>();
        let mut old_accumulator_instances =
            old_accumulator_instances.into_iter().collect::<Vec<_>>();
        let mut num_all_inputs = input_instances.len() + old_accumulator_instances.len();

        let make_zk = proof.hiding_comms.is_some();

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if num_all_inputs == 0 {
            default_input_instance = Some(InputInstanceVar::new_constant(
                sponge.cs(),
                InputInstance::zero(),
            )?);

            input_instances.push(default_input_instance.as_ref().unwrap());
            num_all_inputs += 1;
        }

        // Placeholder input for hiding.
        let placeholder_input_instance;
        if make_zk && num_all_inputs == 1 {
            placeholder_input_instance = Some(InputInstanceVar::new_constant(
                sponge.cs(),
                InputInstance::zero(),
            )?);

            input_instances.push(placeholder_input_instance.as_ref().unwrap());
            num_all_inputs += 1;
        }

        if !Self::check_proof_structure(proof, num_all_inputs) {
            return Ok(Boolean::FALSE);
        }

        let mut all_input_instances = input_instances;
        all_input_instances.append(&mut old_accumulator_instances);

        // Step 1 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut challenges_sponge = sponge;
        absorb_gadget!(
            &mut challenges_sponge,
            &verifier_key.num_supported_elems,
            &all_input_instances,
            &proof.hiding_comms
        );

        let mu_challenges_bits =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_all_inputs, make_zk)?;

        let mu_challenges_var: Vec<NonNativeFieldVar<G::ScalarField, _>> =
            bits_le_to_nonnative(cs.clone(), &mu_challenges_bits).unwrap();
        for i in 0..mu_challenges_var.len() {
            println!(
                "mu challenges var {:?} {:?}",
                i,
                &mu_challenges_var[i].value()
            );
        }

        challenges_sponge.absorb(&proof.product_poly_comm)?;

        let nu_challenges_bits =
            Self::squeeze_nu_challenges(&mut challenges_sponge, num_all_inputs)?;

        let nu_challenges_var: Vec<NonNativeFieldVar<G::ScalarField, _>> =
            bits_le_to_nonnative(cs.clone(), &nu_challenges_bits).unwrap();
        for i in 0..nu_challenges_var.len() {
            println!(
                "nu challenges var {:?} {:?}",
                i,
                &nu_challenges_var[i].value()
            );
        }

        // Steps 2-4 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let accumulator_instance = Self::compute_combined_hp_commitments(
            all_input_instances.as_slice(),
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
    use crate::tests::poseidon_parameters_for_test;
    use ark_relations::r1cs::SynthesisError;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type G = ark_pallas::Affine;
    type C = ark_pallas::constraints::GVar;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = ASForHadamardProducts<G, Sponge>;
    type I = ASForHPTestInput;
    type ASV = ASForHPVerifierGadget<G, C, Sponge, SpongeVar>;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn single_input_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn single_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_input_init_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn no_inputs_init_test_no_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn no_inputs_init_test_zk() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(
            &ASForHPTestParams {
                vector_len: 11,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
            &poseidon_parameters_for_test::<CF>(),
        )
    }
}
