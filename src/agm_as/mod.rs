use crate::data_structures::{Accumulator, Input};
use crate::error::{ASError, BoxedError};
use crate::std::string::ToString;
use crate::std::vec::Vec;
use crate::{AccumulationScheme, AidedAccumulationScheme};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{to_bytes, One, UniformRand, Zero};
use ark_poly_commit::{marlin_pc, Error as PCError, PolynomialCommitment};
use ark_sponge::{absorb_all, CryptographicSponge};
use core::marker::PhantomData;
use digest::Digest;
use marlin_pc::MarlinKZG10;
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

/// Implements an accumulation scheme for a pairing-based polynomial commitment scheme PC_AGM,
/// which described in [KZG10][kzg] and [[CHMMVW20]][marlin].
/// The construction for the accumulation scheme is taken from [[BCMS20]][pcdas].
///
/// [kzg]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
/// [marlin]: https://eprint.iacr.org/2019/104
/// [pcdas]: https://eprint.iacr.org/2020/499
pub struct AGMAccumulationScheme<E: PairingEngine, D: Digest, S: CryptographicSponge<E::Fr>> {
    _engine: PhantomData<E>,
    _digest: PhantomData<D>,
    _sponge: PhantomData<S>,
}

impl<E: PairingEngine, D: Digest, S: CryptographicSponge<E::Fr>> AGMAccumulationScheme<E, D, S> {
    fn new_sponge(for_accumulation_challenge: bool) -> S {
        let mut sponge = S::new();
        sponge.absorb(&for_accumulation_challenge);
        sponge
    }

    /// Accumulates the new inputs and outputs (accumulated_commitments, accumulated_proofs)
    fn accumulate_inputs<'a>(
        verifier_key: &marlin_pc::VerifierKey<E>,
        inputs: &Vec<&InputInstance<E>>,
        accumulation_challenge_powers: &Vec<E::Fr>,
    ) -> Result<(E::G1Projective, E::G1Projective), BoxedError> {
        let vk = &verifier_key.vk;
        let verifier_key_bytes = to_bytes!(verifier_key).unwrap();

        let mut accumulated_commitments = E::G1Projective::zero();
        let mut accumulated_proofs = E::G1Projective::zero();
        for (i, input) in inputs.iter().enumerate() {
            let labeled_commitment = &input.instance.commitment;
            let degree_bound = labeled_commitment.degree_bound();
            let commitment = labeled_commitment.commitment();

            if degree_bound.is_some() != commitment.shifted_comm.is_some() {
                return Err(BoxedError::new(ASError::MalformedInput(
                    "The input's shifted commitment and degree bound exist or not exist together."
                        .to_string(),
                )));
            }

            let eval = &input.instance.evaluation;

            // An element in the summation used to accumulate the commitments from the inputs
            let mut commitment_addend = (commitment.comm.0.into_projective()
                - &vk.g.mul(eval.clone()))
                + &input.proof.w.mul(input.instance.point.clone());

            if let Some(random_v) = &input.proof.random_v {
                commitment_addend -= &vk.gamma_g.mul(random_v.clone());
            }

            if let Some(degree_bound) = degree_bound {
                // The assertion statement above ensures that shifted_comm exists if degree_bound exists.
                let shifted_comm = commitment.shifted_comm.unwrap();
                let shift_power =
                    verifier_key
                        .get_shift_power(degree_bound)
                        .ok_or(BoxedError::new(PCError::UnsupportedDegreeBound(
                            degree_bound,
                        )))?;
                let mut sponge = Self::new_sponge(false);
                absorb_all![&mut sponge; &verifier_key_bytes, &input.instance];

                let opening_challenge = sponge.squeeze_field_elements(1).pop().unwrap();

                let shifted_comm_diff =
                    shifted_comm.0.into_projective() - &shift_power.mul(eval.clone());
                commitment_addend += &shifted_comm_diff.mul(opening_challenge);
            }

            let power = accumulation_challenge_powers[i].clone();
            accumulated_commitments += &commitment_addend.mul(power);
            accumulated_proofs += &input.proof.w.mul(power);
        }

        Ok((accumulated_commitments, accumulated_proofs))
    }

    /// Accumulates inputs and old accumulators into a new accumulator.
    fn compute_accumulator<'a>(
        verifier_key: &marlin_pc::VerifierKey<E>,
        inputs: impl IntoIterator<Item = &'a InputInstance<E>>,
        accumulators: impl IntoIterator<Item = &'a AccumulatorInstance<E>>,
        proof: &Proof<E>,
    ) -> Result<AccumulatorInstance<E>, BoxedError> {
        let inputs: Vec<&InputInstance<E>> = inputs.into_iter().collect();
        let accumulators: Vec<&AccumulatorInstance<E>> = accumulators.into_iter().collect();

        let mut sponge = Self::new_sponge(true);
        sponge.absorb(&to_bytes!(verifier_key).unwrap());
        for input in &inputs {
            sponge.absorb(*input);
        }
        for accumulator in &accumulators {
            sponge.absorb(*accumulator);
        }
        sponge.absorb(proof);

        let accumulation_challenge = sponge.squeeze_field_elements(1).pop().unwrap();

        // Compute the powers of the accumulation challenge, up to a power of
        // (num_inputs + num_accumulators)
        let num_inputs = inputs.len();
        let num_accumulators = accumulators.len();
        let mut accumulation_challenge_powers =
            Vec::with_capacity(num_inputs + num_accumulators + 1);
        let mut r = E::Fr::one();
        for _ in 0..=(num_inputs + num_accumulators) {
            accumulation_challenge_powers.push(r.clone());
            r *= &accumulation_challenge;
        }

        // Accumulate the commitments and proofs from the inputs
        let (mut accumulated_commitments, mut accumulated_proofs) =
            Self::accumulate_inputs(&verifier_key, &inputs, &accumulation_challenge_powers)?;

        // Accumulate everything else
        for (i, acc) in accumulators.into_iter().enumerate() {
            accumulated_commitments += &acc
                .accumulated_commitments
                .mul(accumulation_challenge_powers[num_inputs + i]);
            accumulated_proofs += &acc
                .accumulated_proofs
                .mul(accumulation_challenge_powers[num_inputs + i]);
        }

        accumulated_commitments += &proof
            .accumulated_commitments_randomness
            .mul(accumulation_challenge_powers[num_inputs + num_accumulators]);
        accumulated_proofs += &proof
            .accumulated_proofs_randomness
            .mul(accumulation_challenge_powers[num_inputs + num_accumulators]);

        let mut affines = E::G1Projective::batch_normalization_into_affine(&[
            accumulated_commitments,
            accumulated_proofs,
        ]);

        let accumulated_proofs = affines.pop().unwrap();
        let accumulated_commitments = affines.pop().unwrap();

        let new_accumulator = AccumulatorInstance {
            accumulated_commitments,
            accumulated_proofs,
        };

        Ok(new_accumulator)
    }
}

impl<E: PairingEngine, D: Digest, S: CryptographicSponge<E::Fr>> AidedAccumulationScheme
    for AGMAccumulationScheme<E, D, S>
{
    type PredicateParams = marlin_pc::UniversalParams<E>;
    type PredicateIndex = PredicateIndex;

    type UniversalParams = ();
    type ProverKey = ProverKey<E>;
    type VerifierKey = marlin_pc::VerifierKey<E>;
    type DeciderKey = marlin_pc::VerifierKey<E>;
    type InputInstance = InputInstance<E>;
    type InputWitness = ();
    type AccumulatorInstance = AccumulatorInstance<E>;
    type AccumulatorWitness = ();
    type Proof = Proof<E>;

    type Error = BoxedError;

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let enforced_degree_bounds = predicate_index
            .enforced_degree_bounds
            .as_ref()
            .map(|bounds| bounds.as_slice());
        let trim = MarlinKZG10::<E>::trim(
            predicate_params,
            predicate_index.supported_degree,
            predicate_index.supported_hiding_bound,
            enforced_degree_bounds,
        )
        .map_err(|e| BoxedError::new(e))?;

        let marlin_vk = trim.1;
        let beta_g = trim.0.powers[1].clone();
        let prover_key = ProverKey {
            marlin_vk: marlin_vk.clone(),
            beta_g,
        };

        Ok((prover_key, marlin_vk.clone(), marlin_vk))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = &'a Input<Self>>,
        accumulators: impl IntoIterator<Item = &'a Accumulator<Self>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let inputs = Input::instances(inputs);
        let accumulators = Accumulator::instances(accumulators);

        let rng = rng.ok_or(BoxedError::new(ASError::MissingRng(
            "agm_as prover requires rng".to_string(),
        )))?;
        let randomness = E::Fr::rand(rng);

        let accumulated_commitments_randomness_projective = prover_key.beta_g.mul(randomness);
        let accumulated_proofs_randomness_projective = prover_key.marlin_vk.vk.g.mul(randomness);
        let mut affines = E::G1Projective::batch_normalization_into_affine(&[
            accumulated_commitments_randomness_projective,
            accumulated_proofs_randomness_projective,
        ]);
        let accumulated_proofs_randomness = affines.pop().unwrap();
        let accumulated_commitments_randomness = affines.pop().unwrap();

        let proof = Proof {
            accumulated_commitments_randomness,
            accumulated_proofs_randomness,
        };

        let accumulator_instance =
            Self::compute_accumulator(&prover_key.marlin_vk, inputs, accumulators, &proof)?;
        let accumulator = Accumulator::from_instance(accumulator_instance);

        Ok((accumulator, proof))
    }

    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        inputs: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulators: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let accumulator = Self::compute_accumulator(&verifier_key, inputs, accumulators, proof);
        if accumulator.is_err() {
            return Ok(false);
        }
        Ok(accumulator.unwrap().eq(new_accumulator))
    }

    fn decide<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: &Accumulator<Self>,
    ) -> Result<bool, Self::Error> {
        let accumulator = &accumulator.instance;

        let lhs = E::pairing(
            accumulator.accumulated_commitments.clone(),
            decider_key.vk.h.clone(),
        );

        let rhs = E::pairing(
            accumulator.accumulated_proofs.clone(),
            decider_key.vk.beta_h.clone(),
        );

        Ok(lhs == rhs)
    }
}

impl<E: PairingEngine, D: Digest, S: CryptographicSponge<E::Fr>> AccumulationScheme
    for AGMAccumulationScheme<E, D, S>
{
}

#[cfg(test)]
pub mod tests {
    use crate::agm_as::{
        AGMAccumulationScheme, AGMInstance, AccumulatorInstance, InputInstance, PredicateIndex,
    };
    use crate::data_structures::{Accumulator, Input};
    use crate::tests::{multiple_inputs_test, AccumulationSchemeTestInput};
    use crate::AidedAccumulationScheme;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
    use ark_ff::{to_bytes, UniformRand};
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_poly_commit::{
        marlin_pc, LabeledPolynomial, PCCommitterKey, Polynomial, PolynomialCommitment,
    };
    use ark_sponge::digest_sponge::DigestSponge;
    use ark_sponge::{absorb_all, CryptographicSponge};
    use digest::Digest;
    use rand::distributions::Distribution;
    use rand_core::RngCore;
    use sha2::Sha512;

    pub struct TestParams {
        has_degree_bounds: bool,
        has_hiding_bounds: bool,
    }

    pub struct InputParams<E: PairingEngine> {
        has_hiding_bounds: bool,
        ck: marlin_pc::CommitterKey<E>,
        vk: marlin_pc::VerifierKey<E>,
    }

    pub struct AGMAccumulationSchemeTestInput {}

    impl<E: PairingEngine, D: Digest, S: CryptographicSponge<E::Fr>>
        AccumulationSchemeTestInput<AGMAccumulationScheme<E, D, S>>
        for AGMAccumulationSchemeTestInput
    {
        type TestParams = TestParams;
        type InputParams = InputParams<E>;

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <AGMAccumulationScheme<E, D, S> as AidedAccumulationScheme>::PredicateParams,
            <AGMAccumulationScheme<E, D, S> as AidedAccumulationScheme>::PredicateIndex,
        ) {
            let max_degree = rand::distributions::Uniform::from(1..=128).sample(rng);
            let supported_degree = rand::distributions::Uniform::from(1..=max_degree).sample(rng);
            let predicate_params = MarlinKZG10::<E>::setup(max_degree, rng).unwrap();

            let supported_hiding_bound = if test_params.has_hiding_bounds {
                supported_degree
            } else {
                0usize
            };

            let enforced_degree_bounds: Option<Vec<usize>> = if test_params.has_degree_bounds {
                let degree_bounds = (0..=supported_degree).collect();
                Some(degree_bounds)
            } else {
                None
            };

            let (ck, vk) = MarlinKZG10::<E>::trim(
                &predicate_params,
                supported_degree,
                supported_hiding_bound,
                enforced_degree_bounds.as_ref().map(|v| v.as_slice()),
            )
            .unwrap();

            let input_params = InputParams {
                has_hiding_bounds: test_params.has_hiding_bounds,
                ck,
                vk,
            };

            let predicate_index = PredicateIndex {
                supported_degree,
                supported_hiding_bound,
                enforced_degree_bounds,
            };

            (input_params, predicate_params, predicate_index)
        }

        fn generate_starting_accumulators(
            input_params: &Self::InputParams,
            num_accumulators: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Accumulator<AGMAccumulationScheme<E, D, S>>> {
            let ck = &input_params.ck;

            let mut accumulators = Vec::with_capacity(num_accumulators);
            for _ in 0..num_accumulators {
                let power = E::Fr::rand(rng);
                let accumulated_commitments = ck.powers[1].mul(power);
                let accumulated_proofs = ck.powers[0].mul(power);
                let mut affines = E::G1Projective::batch_normalization_into_affine(&[
                    accumulated_commitments,
                    accumulated_proofs,
                ]);

                let accumulated_proofs = affines.pop().unwrap();
                let accumulated_commitments = affines.pop().unwrap();
                let accumulator = AccumulatorInstance {
                    accumulated_commitments,
                    accumulated_proofs,
                };
                accumulators.push(accumulator);
            }

            Accumulator::from_instances(accumulators).collect()
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<AGMAccumulationScheme<E, D, S>>> {
            let ck = &input_params.ck;
            let vk = &input_params.vk;
            let vk_bytes = to_bytes!(vk).unwrap();

            let mut labeled_polynomials = Vec::with_capacity(num_inputs);
            for i in 0..num_inputs {
                let degree =
                    rand::distributions::Uniform::from(1..ck.supported_degree()).sample(rng);

                let label = format!("Input{}", i);
                let polynomial = Polynomial::rand(degree, rng);
                let degree_bound = if input_params.ck.enforced_degree_bounds.is_some() {
                    Some(polynomial.degree())
                } else {
                    None
                };

                let hiding_bound = if input_params.has_hiding_bounds {
                    Some(polynomial.degree())
                } else {
                    None
                };

                let labeled_polynomial =
                    LabeledPolynomial::new(label, polynomial, degree_bound, hiding_bound);
                labeled_polynomials.push(labeled_polynomial);
            }
            let (labeled_commitments, randomness) =
                MarlinKZG10::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

            let mut inputs = Vec::with_capacity(num_inputs);
            for ((labeled_polynomial, labeled_commitment), rand) in labeled_polynomials
                .into_iter()
                .zip(labeled_commitments)
                .zip(randomness)
            {
                let point = E::Fr::rand(rng);
                let evaluation = labeled_polynomial.evaluate(point);

                let degree_bound = if input_params.ck.enforced_degree_bounds.is_some() {
                    Some(labeled_polynomial.degree())
                } else {
                    None
                };

                let instance = AGMInstance {
                    commitment: labeled_commitment.clone(),
                    degree_bound,
                    point,
                    evaluation,
                };

                let mut sponge = AGMAccumulationScheme::<E, D, S>::new_sponge(false);
                absorb_all![&mut sponge; &vk_bytes, &instance];
                let challenge = sponge.squeeze_field_elements(1).pop().unwrap();

                let proof = MarlinKZG10::open(
                    ck,
                    vec![&labeled_polynomial],
                    vec![&labeled_commitment],
                    point,
                    challenge,
                    vec![&rand],
                    Some(rng),
                )
                .unwrap();

                let input = InputInstance {
                    instance: AGMInstance {
                        commitment: labeled_commitment,
                        degree_bound: labeled_polynomial.degree_bound(),
                        point,
                        evaluation,
                    },
                    proof,
                };

                inputs.push(input);
            }

            Input::from_instances(inputs).collect()
        }
    }

    type AS = AGMAccumulationScheme<Bls12_381, Sha512, DigestSponge<Fr, Sha512>>;
    type I = AGMAccumulationSchemeTestInput;

    #[test]
    pub fn agm_multiple_inputs_test() {
        let test_params = TestParams {
            has_degree_bounds: true,
            has_hiding_bounds: true,
        };

        assert!(multiple_inputs_test::<AS, I>(&test_params).is_ok());
    }
}
