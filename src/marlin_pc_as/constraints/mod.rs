use crate::constraints::{ASVerifierGadget, AtomicASVerifierGadget};
use crate::marlin_pc_as::{
    AtomicASForMarlinPC, InputInstance, CHALLENGE_SIZE, MARLIN_PC_PROTOCOL_NAME, PROTOCOL_NAME,
};

use ark_ec::PairingEngine;
use ark_poly_commit::marlin::marlin_pc;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::absorb_gadget;
use ark_sponge::constraints::{AbsorbableGadget, CryptographicSpongeVar};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;

mod data_structures;
pub use data_structures::*;

/// The verifier gadget of [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
pub struct AtomicASForMarlinPCVerifierGadget<E, PV, S, SV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq> + 'static,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
    PV::G2Var: AbsorbableGadget<E::Fq>,
    S: CryptographicSponge<E::Fq>,
    SV: CryptographicSpongeVar<E::Fq, S>,
{
    _pairing_engine_phantom: PhantomData<E>,
    _pairing_var_phantom: PhantomData<PV>,
    _sponge_phantom: PhantomData<S>,
    _sponge_var_phantom: PhantomData<SV>,
}

impl<E, PV, S, SV> AtomicASForMarlinPCVerifierGadget<E, PV, S, SV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq> + 'static,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
    PV::G2Var: AbsorbableGadget<E::Fq>,
    S: CryptographicSponge<E::Fq>,
    SV: CryptographicSpongeVar<E::Fq, S>,
{
    /// Squeezes `num_challenges` accumulation challenges, where the first challenge is one.
    fn squeeze_accumulation_challenges(
        sponge: &mut SV,
        num_challenges: usize,
    ) -> Result<Vec<Vec<Boolean<E::Fq>>>, SynthesisError> {
        let mut challenges = Vec::with_capacity(num_challenges);
        challenges.push(vec![Boolean::TRUE]);

        if num_challenges > 1 {
            let rest_of_challenges_bits =
                sponge.squeeze_bits(CHALLENGE_SIZE * (num_challenges - 1))?;
            rest_of_challenges_bits
                .chunks(CHALLENGE_SIZE)
                .for_each(|c| {
                    challenges.push(c.to_vec());
                });
        }

        Ok(challenges)
    }

    /// Accumulates inputs into a single tuple: (accumulated_commitment, accumulated_proof)
    fn accumulate_inputs<'a>(
        cs: ConstraintSystemRef<E::Fq>,
        verifier_key: &marlin_pc::VerifierKeyVar<E, PV>,
        inputs: &Vec<&InputInstanceVar<E, PV>>,
        accumulation_challenges: &Vec<Vec<Boolean<E::Fq>>>,
        mut pc_sponge: SV,
    ) -> Result<Option<(PV::G1Var, PV::G1Var)>, SynthesisError> {
        assert!(inputs.len() <= accumulation_challenges.len());
        pc_sponge.absorb(&verifier_key)?;

        let mut accumulated_commitment = PV::G1Var::zero();
        let mut accumulated_proof = PV::G1Var::zero();
        for (i, input) in inputs.iter().enumerate() {
            let labeled_commitment = &input.marlin_pc_instance.commitment;
            let degree_bound = labeled_commitment.degree_bound.as_ref();
            let commitment = &labeled_commitment.commitment;

            if degree_bound.is_some() != commitment.shifted_comm.is_some() {
                return Ok(None);
            }

            let eval = &input.marlin_pc_instance.evaluation;

            // An element in the summation used to accumulate the commitments from the inputs
            let mut commitment_addend: PV::G1Var = (commitment.comm.clone()
                - &verifier_key.g.scalar_mul_le(eval.iter())?)
                + &input
                    .marlin_pc_proof
                    .w
                    .scalar_mul_le(input.marlin_pc_instance.point.iter())?;

            if let Some(random_v) = &input.marlin_pc_proof.random_v {
                commitment_addend -= &verifier_key
                    .gamma_g
                    .scalar_mul_le(random_v.to_bits_le()?.iter())?;
            }

            if let Some(degree_bound) = degree_bound {
                // The assertion statement above ensures that shifted_comm exists if degree_bound exists.
                let shifted_comm = commitment.shifted_comm.clone().unwrap();
                let shift_power = verifier_key.get_shift_power(cs.clone(), degree_bound);

                if shift_power.is_none() {
                    return Ok(None);
                }

                let shift_power = shift_power.unwrap();

                let mut opening_challenge_sponge = pc_sponge.clone();
                opening_challenge_sponge.absorb(&input.marlin_pc_instance)?;

                let (_, mut opening_challenge_bits) = opening_challenge_sponge
                    .squeeze_nonnative_field_elements_with_sizes::<E::Fr>(
                        vec![FieldElementSize::Truncated(CHALLENGE_SIZE)].as_slice(),
                    )?;

                let opening_challenge_bits = opening_challenge_bits.pop().unwrap();

                let shifted_comm_diff: PV::G1Var =
                    shifted_comm - &shift_power.scalar_mul_le(eval.iter())?;

                commitment_addend +=
                    &shifted_comm_diff.scalar_mul_le(opening_challenge_bits.iter())?;
            }

            let challenge = accumulation_challenges[i].clone();
            accumulated_commitment += &commitment_addend.scalar_mul_le(challenge.iter())?;
            accumulated_proof += &input.marlin_pc_proof.w.scalar_mul_le(challenge.iter())?;
        }

        Ok(Some((accumulated_commitment, accumulated_proof)))
    }

    /// Accumulates inputs and old accumulators into a new accumulator.
    fn compute_accumulator(
        cs: ConstraintSystemRef<E::Fq>,
        verifier_key: &marlin_pc::VerifierKeyVar<E, PV>,
        inputs: &Vec<&InputInstanceVar<E, PV>>,
        accumulators: &Vec<&AccumulatorInstanceVar<E, PV>>,
        proof: &ProofVar<E, PV>,
        sponge: SV,
    ) -> Result<Option<AccumulatorInstanceVar<E, PV>>, SynthesisError> {
        let mut accumulation_challenge_sponge = sponge.fork(&PROTOCOL_NAME)?;
        absorb_gadget!(
            &mut accumulation_challenge_sponge,
            verifier_key,
            inputs,
            accumulators,
            proof
        );

        let num_inputs = inputs.len();
        let num_accumulators = accumulators.len();

        let accumulation_challenges: Vec<Vec<Boolean<E::Fq>>> =
            Self::squeeze_accumulation_challenges(
                &mut accumulation_challenge_sponge,
                num_inputs + num_accumulators + if proof.randomness.is_some() { 1 } else { 0 },
            )?;

        // Accumulate the commitments and proofs from the inputs
        let accumulated_inputs = Self::accumulate_inputs(
            cs.clone(),
            &verifier_key,
            &inputs,
            &accumulation_challenges,
            sponge.fork(&MARLIN_PC_PROTOCOL_NAME)?,
        )?;

        if accumulated_inputs.is_none() {
            return Ok(None);
        }

        let (mut accumulated_commitment, mut accumulated_proof) = accumulated_inputs.unwrap();

        // Accumulate the accumulators
        for (i, acc) in accumulators.into_iter().enumerate() {
            accumulated_commitment += &acc
                .accumulated_commitment
                .scalar_mul_le(accumulation_challenges[num_inputs + i].iter())?;
            accumulated_proof += &acc
                .accumulated_proof
                .scalar_mul_le(accumulation_challenges[num_inputs + i].iter())?;
        }

        // Apply the randomness from the proof
        if let Some(randomness) = proof.randomness.as_ref() {
            accumulated_commitment += randomness
                .accumulated_commitment_randomness
                .scalar_mul_le(accumulation_challenges[num_inputs + num_accumulators].iter())?;

            accumulated_proof += randomness
                .accumulated_proof_randomness
                .scalar_mul_le(accumulation_challenges[num_inputs + num_accumulators].iter())?;
        }

        let new_accumulator = AccumulatorInstanceVar {
            accumulated_commitment,
            accumulated_proof,
        };

        Ok(Some(new_accumulator))
    }
}

impl<E, PV, S, SV> ASVerifierGadget<E::Fq, S, SV, AtomicASForMarlinPC<E, S>>
    for AtomicASForMarlinPCVerifierGadget<E, PV, S, SV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq> + 'static,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
    PV::G2Var: AbsorbableGadget<E::Fq>,
    S: CryptographicSponge<E::Fq>,
    SV: CryptographicSpongeVar<E::Fq, S>,
{
    type VerifierKey = marlin_pc::VerifierKeyVar<E, PV>;
    type InputInstance = InputInstanceVar<E, PV>;
    type AccumulatorInstance = AccumulatorInstanceVar<E, PV>;
    type Proof = ProofVar<E, PV>;

    fn verify<'a>(
        cs: ConstraintSystemRef<<E as PairingEngine>::Fq>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<SV>,
    ) -> Result<Boolean<<E as PairingEngine>::Fq>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| SV::new(cs.clone()));

        let mut inputs = input_instances.into_iter().collect::<Vec<_>>();
        let old_accumulators = old_accumulator_instances.into_iter().collect::<Vec<_>>();

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if inputs.is_empty() && old_accumulators.is_empty() {
            default_input_instance = Some(InputInstanceVar::new_constant(
                cs.clone(),
                InputInstance::zero(),
            )?);
            inputs.push(default_input_instance.as_ref().unwrap());
        }

        let test_accumulator = Self::compute_accumulator(
            cs.clone(),
            &verifier_key,
            &inputs,
            &old_accumulators,
            &proof,
            sponge,
        );

        if test_accumulator.is_err() {
            return Ok(Boolean::FALSE);
        }

        let test_accumulator = test_accumulator.unwrap();

        if test_accumulator.is_none() {
            return Ok(Boolean::FALSE);
        }

        let test_accumulator = test_accumulator.unwrap();

        Ok(test_accumulator.is_eq(&new_accumulator_instance)?)
    }
}

impl<E, PV, S, SV> AtomicASVerifierGadget<E::Fq, S, SV, AtomicASForMarlinPC<E, S>>
    for AtomicASForMarlinPCVerifierGadget<E, PV, S, SV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq> + 'static,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
    PV::G2Var: AbsorbableGadget<E::Fq>,
    S: CryptographicSponge<E::Fq>,
    SV: CryptographicSpongeVar<E::Fq, S>,
{
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::tests::ASVerifierGadgetTests;
    use crate::marlin_pc_as::constraints::AtomicASForMarlinPCVerifierGadget;
    use crate::marlin_pc_as::tests::{AtomicASForMarlinPCTestInput, AtomicASForMarlinPCTestParams};
    use crate::marlin_pc_as::AtomicASForMarlinPC;
    use ark_bls12_377::Bls12_377;
    use ark_relations::r1cs::SynthesisError;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    type E = Bls12_377;
    type PV = ark_bls12_377::constraints::PairingVar;
    type CF = ark_bls12_377::Fq;

    type Sponge = PoseidonSponge<CF>;
    type SpongeVar = PoseidonSpongeVar<CF>;

    type AS = AtomicASForMarlinPC<E, Sponge>;
    type I = AtomicASForMarlinPCTestInput<E, Sponge>;
    type ASV = AtomicASForMarlinPCVerifierGadget<E, PV, Sponge, SpongeVar>;

    type Tests = ASVerifierGadgetTests<CF, Sponge, SpongeVar, AS, ASV, I>;

    #[test]
    pub fn single_input_init_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError>
    {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk_no_degree_bounds() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn single_input_init_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk_degree_bounds() -> Result<(), SynthesisError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }
}
