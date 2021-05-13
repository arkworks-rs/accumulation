use crate::data_structures::Accumulator;
use crate::error::{ASError, BoxedError};
use crate::{AccumulationScheme, AccumulatorRef, AtomicAccumulationScheme, InputRef, MakeZK};

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{One, UniformRand, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{marlin_pc, Error as PCError, PolynomialCommitment};
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::rand::RngCore;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use core::marker::PhantomData;
use marlin_pc::MarlinKZG10;

mod data_structures;
pub use data_structures::*;

/// The verifier constraints of [`AtomicASForMarlinPC`].
#[cfg(feature = "r1cs")]
pub mod constraints;

pub(crate) const MARLIN_PC_PROTOCOL_NAME: &[u8] = b"MARLIN-PC-2020";
pub(crate) const PROTOCOL_NAME: &[u8] = b"AS-FOR-MARLIN-PC-2020";

/// Size of squeezed challenges in terms of number of bits.
pub(crate) const CHALLENGE_SIZE: usize = 128;

/// An accumulation scheme for a polynomial commitment scheme based on bilinear groups.
/// This implementation is specialized for [`MarlinKZG10`][marlin-pc].
/// The construction is described in detail in Section 8 of [\[BCMS20\]][\[BCMS20\]].
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 10.1 in [\[BCLMS20\]][bclms20] for more details.
///
/// [marlin-pc]: ark_poly_commit::marlin_pc::MarlinKZG10
/// [\[BCMS20\]]: https://eprint.iacr.org/2020/499
/// [bclms20]: https://eprint.iacr.org/2020/1618
///
/// # Example Input
/// ```
///
/// use ark_accumulation::marlin_pc_as::{AtomicASForMarlinPC, InputInstance, MarlinPCInstance};
/// use ark_accumulation::Input;
/// use ark_ec::{AffineCurve, PairingEngine};
/// use ark_ff::Field;
/// use ark_poly::univariate::DensePolynomial;
/// use ark_poly_commit::marlin_pc::MarlinKZG10;
/// use ark_poly_commit::{marlin_pc, LabeledCommitment, PolynomialCommitment};
/// use ark_sponge::{Absorbable, CryptographicSponge};
///
/// // An accumulation input for this scheme is formed from:
/// // 1. A MarlinPC commitment to a polynomial:             `comm`
/// // 2. A point where the polynomial will be evaluated at: `point`
/// // 3. The evaluation of the polynomial at the point:     `eval`
/// // 4. The MarlinPC opening at the point:                 `proof`
/// fn new_accumulation_input<E, S>(
///     comm: LabeledCommitment<marlin_pc::Commitment<E>>,
///     point: E::Fr,
///     eval: E::Fr,
///     proof: <MarlinKZG10<E, DensePolynomial<E::Fr>> as PolynomialCommitment<
///         E::Fr,
///         DensePolynomial<E::Fr>,
///     >>::Proof,
/// ) -> Input<E::Fq, S, AtomicASForMarlinPC<E, S>>
///     where
///         E: PairingEngine,
///         E::G1Affine: Absorbable<E::Fq>,
///         E::G2Affine: Absorbable<E::Fq>,
///         E::Fq: Absorbable<E::Fq>,
///         S: CryptographicSponge<E::Fq>,
/// {
///     let instance = InputInstance {
///         marlin_pc_instance: MarlinPCInstance {
///             commitment: comm,
///             point,
///             evaluation: eval,
///         },
///         marlin_pc_proof: proof,
///     };
///
///     let witness = ();
///
///     Input::<_, _, AtomicASForMarlinPC<E, S>> { instance, witness }
/// }
/// ```
pub struct AtomicASForMarlinPC<E, S>
where
    E: PairingEngine,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    S: CryptographicSponge<E::Fq>,
{
    _engine_phantom: PhantomData<E>,
    _sponge_phantom: PhantomData<S>,
}

impl<E, S> AtomicASForMarlinPC<E, S>
where
    E: PairingEngine,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    S: CryptographicSponge<E::Fq>,
{
    /// Generate the randomness used by the accumulation prover.
    fn generate_prover_randomness(
        prover_key: &ProverKey<E>,
        rng: &mut dyn RngCore,
    ) -> Randomness<E> {
        let randomness = E::Fr::rand(rng);

        let accumulated_commitment_randomness_projective = prover_key.beta_g.mul(randomness);

        let accumulated_proof_randomness_projective = prover_key.marlin_vk.vk.g.mul(randomness);

        let mut affines = E::G1Projective::batch_normalization_into_affine(&[
            accumulated_commitment_randomness_projective,
            accumulated_proof_randomness_projective,
        ]);

        let accumulated_proof_randomness = affines.pop().unwrap();

        let accumulated_commitment_randomness = affines.pop().unwrap();

        Randomness {
            accumulated_commitment_randomness,
            accumulated_proof_randomness,
        }
    }

    /// Squeezes `num_challenges` accumulation challenges, where the first challenge is one.
    fn squeeze_accumulation_challenges(sponge: &mut S, num_challenges: usize) -> Vec<E::Fr> {
        let mut challenges = Vec::with_capacity(num_challenges);
        challenges.push(E::Fr::one());

        if num_challenges > 1 {
            let mut rest_of_challenges = sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(CHALLENGE_SIZE); num_challenges - 1].as_slice(),
            );

            challenges.append(&mut rest_of_challenges);
        }

        challenges
    }

    /// Accumulates inputs into a single tuple: (accumulated_commitment, accumulated_proof)
    /// Steps 7a, 7c of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
    fn accumulate_inputs<'a>(
        verifier_key: &marlin_pc::VerifierKey<E>,
        inputs: &Vec<&InputInstance<E>>,
        accumulation_challenges: &Vec<E::Fr>,
        mut pc_sponge: S,
    ) -> Result<(E::G1Projective, E::G1Projective), BoxedError> {
        assert!(inputs.len() <= accumulation_challenges.len());
        pc_sponge.absorb(&verifier_key);

        let kzg10_vk = &verifier_key.vk;
        let mut accumulated_commitment = E::G1Projective::zero();
        let mut accumulated_proof = E::G1Projective::zero();
        for (i, input) in inputs.iter().enumerate() {
            let labeled_commitment = &input.marlin_pc_instance.commitment;
            let degree_bound = labeled_commitment.degree_bound();
            let commitment = labeled_commitment.commitment();

            if degree_bound.is_some() != commitment.shifted_comm.is_some() {
                return Err(BoxedError::new(ASError::MalformedInput(
                    "The input's shifted commitment and degree bound exist or not exist together."
                        .to_string(),
                )));
            }

            // Step 7a of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
            let eval = &input.marlin_pc_instance.evaluation;

            // An element in the summation used to accumulate the commitments from the inputs
            let mut commitment_addend = (commitment.comm.0.into_projective()
                - &kzg10_vk.g.mul(eval.clone()))
                + &input
                    .marlin_pc_proof
                    .w
                    .mul(input.marlin_pc_instance.point.clone());

            if let Some(random_v) = &input.marlin_pc_proof.random_v {
                commitment_addend -= &kzg10_vk.gamma_g.mul(random_v.clone());
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

                let mut opening_challenge_sponge = pc_sponge.clone();
                opening_challenge_sponge.absorb(&input.marlin_pc_instance);

                let opening_challenge: E::Fr = opening_challenge_sponge
                    .squeeze_nonnative_field_elements_with_sizes(
                        vec![FieldElementSize::Truncated(CHALLENGE_SIZE)].as_slice(),
                    )
                    .pop()
                    .unwrap();

                let shifted_comm_diff =
                    shifted_comm.0.into_projective() - &shift_power.mul(eval.clone());

                commitment_addend += &shifted_comm_diff.mul(opening_challenge.into());
            }

            let challenge = accumulation_challenges[i].clone();

            accumulated_commitment += &commitment_addend.mul(challenge.into());

            // Step 7c of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
            accumulated_proof += &input.marlin_pc_proof.w.mul(challenge.into());
        }

        Ok((accumulated_commitment, accumulated_proof))
    }

    /// Accumulates inputs and old accumulators into a new accumulator from optional randomness.
    fn compute_accumulator(
        verifier_key: &marlin_pc::VerifierKey<E>,
        inputs: &Vec<&InputInstance<E>>,
        accumulators: &Vec<&AccumulatorInstance<E>>,
        proof: Option<&Randomness<E>>,
        sponge: S,
    ) -> Result<AccumulatorInstance<E>, BoxedError> {
        // Step 6 of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
        let mut accumulation_challenge_sponge = sponge.fork(&PROTOCOL_NAME);
        absorb!(
            &mut accumulation_challenge_sponge,
            verifier_key,
            inputs,
            accumulators,
            proof
        );

        let num_inputs = inputs.len();
        let num_accumulators = accumulators.len();

        let accumulation_challenges: Vec<E::Fr> = Self::squeeze_accumulation_challenges(
            &mut accumulation_challenge_sponge,
            num_inputs + num_accumulators + if proof.is_some() { 1 } else { 0 },
        );

        // Steps 7a, 7c of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
        // Accumulate the old commitments and proofs from the inputs
        let (mut accumulated_commitment, mut accumulated_proof) = Self::accumulate_inputs(
            &verifier_key,
            &inputs,
            &accumulation_challenges,
            sponge.fork(&MARLIN_PC_PROTOCOL_NAME),
        )?;

        // Step 7b of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
        // Accumulate the accumulators
        for (i, acc) in accumulators.into_iter().enumerate() {
            accumulated_commitment += &acc
                .accumulated_commitment
                .mul(accumulation_challenges[num_inputs + i]);
            accumulated_proof += &acc
                .accumulated_proof
                .mul(accumulation_challenges[num_inputs + i]);
        }

        // Step 7c of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
        // Apply the randomness from the proof
        if let Some(randomness) = proof {
            accumulated_commitment += randomness
                .accumulated_commitment_randomness
                .mul(accumulation_challenges[num_inputs + num_accumulators]);

            accumulated_proof += randomness
                .accumulated_proof_randomness
                .mul(accumulation_challenges[num_inputs + num_accumulators]);
        }

        // Step 8 of the scheme's prover and verifier common subroutine, as detailed in BCMS20.
        // Convert everything into affine and form a new accumulator instance.
        let mut affines = E::G1Projective::batch_normalization_into_affine(&[
            accumulated_commitment,
            accumulated_proof,
        ]);

        let accumulated_proof = affines.pop().unwrap();
        let accumulated_commitment = affines.pop().unwrap();

        let new_accumulator = AccumulatorInstance {
            accumulated_commitment,
            accumulated_proof,
        };

        Ok(new_accumulator)
    }
}

impl<E, S> AccumulationScheme<E::Fq, S> for AtomicASForMarlinPC<E, S>
where
    E: PairingEngine,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    S: CryptographicSponge<E::Fq>,
{
    type PublicParameters = ();
    type PredicateParams = marlin_pc::UniversalParams<E>;
    type PredicateIndex = PredicateIndex;

    type ProverKey = ProverKey<E>;
    type VerifierKey = marlin_pc::VerifierKey<E>;
    type DeciderKey = marlin_pc::VerifierKey<E>;

    type InputInstance = InputInstance<E>;
    type InputWitness = ();

    type AccumulatorInstance = AccumulatorInstance<E>;
    type AccumulatorWitness = ();

    type Proof = Option<Randomness<E>>;

    type Error = BoxedError;

    fn setup(_rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error> {
        Ok(())
    }

    fn index(
        _public_params: &Self::PublicParameters,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let enforced_degree_bounds = predicate_index
            .enforced_degree_bounds
            .as_ref()
            .map(|bounds| bounds.as_slice());

        let trim = MarlinKZG10::<E, DensePolynomial<E::Fr>>::trim(
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

    /// Accumulates inputs and past accumulators. Additionally outputs a proof attesting that the
    /// new accumulator was computed properly from the inputs and old accumulators.
    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, E::Fq, S, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, E::Fq, S, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<E::Fq, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let mut inputs: Vec<&InputInstance<E>> = InputRef::<_, _, Self>::instances(inputs)
            .into_iter()
            .collect::<Vec<_>>();

        let old_accumulators = AccumulatorRef::<_, _, Self>::instances(old_accumulators)
            .into_iter()
            .collect::<Vec<_>>();

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if inputs.is_empty() && old_accumulators.is_empty() {
            default_input_instance = Some(InputInstance::zero());
            inputs.push(default_input_instance.as_ref().unwrap());
        }

        let (make_zk_enabled, rng) = make_zk.into_components();
        if !make_zk_enabled {
            // Check that none of the inputs to be accumulated requires hiding.
            for input in &inputs {
                if input.marlin_pc_proof.random_v.is_some() {
                    return Err(BoxedError::new(ASError::MissingRng(
                        "Accumulating inputs with hiding requires rng.".to_string(),
                    )));
                }
            }
        }

        // Generate the prover randomness as the proof.
        let proof = if make_zk_enabled {
            Some(Self::generate_prover_randomness(prover_key, rng.unwrap()))
        } else {
            None
        };

        // Compute an accumulator from the newly generated proof.
        let accumulator_instance = Self::compute_accumulator(
            &prover_key.marlin_vk,
            &inputs,
            &old_accumulators,
            proof.as_ref(),
            sponge,
        )?;

        let accumulator = Accumulator::<_, _, Self> {
            instance: accumulator_instance,
            witness: (),
        };

        Ok((accumulator, proof))
    }

    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let mut inputs = input_instances.into_iter().collect::<Vec<_>>();
        let old_accumulators = old_accumulator_instances.into_iter().collect::<Vec<_>>();

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if inputs.is_empty() && old_accumulators.is_empty() {
            default_input_instance = Some(InputInstance::zero());
            inputs.push(default_input_instance.as_ref().unwrap());
        }

        // Compute an accumulator from the proof.
        let test_accumulator = Self::compute_accumulator(
            &verifier_key,
            &inputs,
            &old_accumulators,
            proof.as_ref(),
            sponge,
        );

        if test_accumulator.is_err() {
            return Ok(false);
        }

        Ok(test_accumulator.unwrap().eq(new_accumulator_instance))
    }

    fn decide<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, E::Fq, S, Self>,
        _sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let accumulator = &accumulator.instance;

        let lhs = E::pairing(
            accumulator.accumulated_commitment.clone(),
            decider_key.vk.h.clone(),
        );

        let rhs = E::pairing(
            accumulator.accumulated_proof.clone(),
            decider_key.vk.beta_h.clone(),
        );

        Ok(lhs == rhs)
    }
}

impl<E, S> AtomicAccumulationScheme<E::Fq, S> for AtomicASForMarlinPC<E, S>
where
    E: PairingEngine,
    E::G1Affine: Absorbable<E::Fq>,
    E::G2Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
    S: CryptographicSponge<E::Fq>,
{
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::marlin_pc_as::{
        AtomicASForMarlinPC, InputInstance, MarlinPCInstance, PredicateIndex, CHALLENGE_SIZE,
        MARLIN_PC_PROTOCOL_NAME,
    };
    use crate::tests::{ASTestInput, ASTests, TestParameters};
    use crate::AccumulationScheme;
    use ark_bls12_377::Bls12_377;
    use ark_ec::PairingEngine;
    use ark_ff::UniformRand;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_poly_commit::UVPolynomial;
    use ark_poly_commit::{marlin_pc, LabeledPolynomial, PCCommitterKey, PolynomialCommitment};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
    use ark_std::marker::PhantomData;
    use ark_std::rand::RngCore;

    pub struct AtomicASForMarlinPCTestParams {
        pub(crate) max_degree: usize,
        pub(crate) has_degree_bounds: bool,
        pub(crate) has_hiding_bounds: bool,
    }

    impl TestParameters for AtomicASForMarlinPCTestParams {
        fn make_zk(&self) -> bool {
            self.has_hiding_bounds
        }
    }

    pub struct AtomicASForMarlinPCTestInputParams<E: PairingEngine> {
        has_hiding_bounds: bool,
        ck: marlin_pc::CommitterKey<E>,
        vk: marlin_pc::VerifierKey<E>,
    }

    pub struct AtomicASForMarlinPCTestInput<E: PairingEngine, S: CryptographicSponge<E::Fq>> {
        _engine: PhantomData<E>,
        _sponge: PhantomData<S>,
    }

    impl<E, S> ASTestInput<E::Fq, S, AtomicASForMarlinPC<E, S>> for AtomicASForMarlinPCTestInput<E, S>
    where
        E: PairingEngine,
        E::G1Affine: Absorbable<E::Fq>,
        E::G2Affine: Absorbable<E::Fq>,
        E::Fq: Absorbable<E::Fq>,
        S: CryptographicSponge<E::Fq>,
    {
        type TestParams = AtomicASForMarlinPCTestParams;
        type InputParams = AtomicASForMarlinPCTestInputParams<E>;

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <AtomicASForMarlinPC<E, S> as AccumulationScheme<E::Fq, S>>::PredicateParams,
            <AtomicASForMarlinPC<E, S> as AccumulationScheme<E::Fq, S>>::PredicateIndex,
        ) {
            let supported_degree = test_params.max_degree;
            let predicate_params =
                MarlinKZG10::<E, DensePolynomial<E::Fr>>::setup(supported_degree, None, rng)
                    .unwrap();

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

            let (ck, vk) = MarlinKZG10::<E, DensePolynomial<E::Fr>>::trim(
                &predicate_params,
                supported_degree,
                supported_hiding_bound,
                enforced_degree_bounds.as_ref().map(|v| v.as_slice()),
            )
            .unwrap();

            let input_params = AtomicASForMarlinPCTestInputParams {
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

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<E::Fq, S, AtomicASForMarlinPC<E, S>>> {
            let ck = &input_params.ck;
            let vk = &input_params.vk;

            let mut challenge_sponge = S::new().fork(&MARLIN_PC_PROTOCOL_NAME);
            challenge_sponge.absorb(vk);

            let labeled_polynomials: Vec<LabeledPolynomial<E::Fr, DensePolynomial<E::Fr>>> = (0
                ..num_inputs)
                .map(|i| {
                    let degree = ck.supported_degree();
                    let label = format!("Input{}", i);
                    let polynomial = DensePolynomial::rand(degree, rng);

                    let hiding_bound = if input_params.has_hiding_bounds {
                        Some(degree)
                    } else {
                        None
                    };

                    let degree_bound = if input_params.ck.enforced_degree_bounds.is_some() {
                        Some(degree)
                    } else {
                        None
                    };

                    let labeled_polynomial =
                        LabeledPolynomial::new(label, polynomial, degree_bound, hiding_bound);

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, randomness) =
                MarlinKZG10::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

            let mut inputs = Vec::with_capacity(num_inputs);
            for ((labeled_polynomial, labeled_commitment), rand) in labeled_polynomials
                .into_iter()
                .zip(labeled_commitments)
                .zip(randomness)
            {
                let point = E::Fr::rand(rng);
                let evaluation = labeled_polynomial.evaluate(&point);

                let instance = MarlinPCInstance {
                    commitment: labeled_commitment.clone(),
                    point,
                    evaluation,
                };

                let mut pc_sponge = challenge_sponge.clone();
                pc_sponge.absorb(&instance);

                let challenge: E::Fr = pc_sponge
                    .squeeze_nonnative_field_elements_with_sizes(
                        vec![FieldElementSize::Truncated(CHALLENGE_SIZE)].as_slice(),
                    )
                    .pop()
                    .unwrap();

                let proof = MarlinKZG10::open(
                    ck,
                    vec![&labeled_polynomial],
                    vec![&labeled_commitment],
                    &point,
                    challenge,
                    vec![&rand],
                    Some(rng),
                )
                .unwrap();

                let input = InputInstance {
                    marlin_pc_instance: MarlinPCInstance {
                        commitment: labeled_commitment,
                        point,
                        evaluation,
                    },
                    marlin_pc_proof: proof,
                };

                inputs.push(input);
            }

            inputs
                .into_iter()
                .map(|input| Input::<_, _, AtomicASForMarlinPC<E, S>> {
                    instance: input,
                    witness: (),
                })
                .collect()
        }
    }

    type E = Bls12_377;
    type CF = ark_bls12_377::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = AtomicASForMarlinPC<E, Sponge>;
    type I = AtomicASForMarlinPCTestInput<E, Sponge>;

    type Tests = ASTests<CF, Sponge, AS, I>;

    #[test]
    pub fn single_input_init_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk_no_degree_bounds() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: false,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn single_input_init_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn single_input_init_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::single_input_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_input_init_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }

    #[test]
    pub fn no_inputs_init_test_no_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: false,
        })
    }

    #[test]
    pub fn no_inputs_init_test_zk_degree_bounds() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(&AtomicASForMarlinPCTestParams {
            max_degree: 11,
            has_degree_bounds: true,
            has_hiding_bounds: true,
        })
    }
}
