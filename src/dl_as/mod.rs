use crate::data_structures::{Accumulator, AccumulatorRef, Input, InputRef};
use crate::error::{ASError, BoxedError};
use crate::std::ops::Mul;
use crate::std::string::ToString;
use crate::std::vec::Vec;
use crate::{AccumulationScheme, AidedAccumulationScheme};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{to_bytes, One, PrimeField, UniformRand, Zero};
use ark_poly_commit::ipa_pc::{InnerProductArgPC, SuccinctCheckPolynomial};
use ark_poly_commit::{
    ipa_pc, Error as PCError, LabeledCommitment, LabeledPolynomial, PCVerifierKey,
    PolynomialCommitment, PolynomialLabel, UVPolynomial,
};
use ark_relations::r1cs::ToConstraintField;
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use digest::Digest;
use rand_core::{RngCore, SeedableRng};

mod data_structures;
pub use data_structures::*;

// Alias for readability
type FinalCommKey<G> = G;
pub type PCDL<G, P, D, CF, S> = InnerProductArgPC<G, D, P, CF, SpongeForPC<CF, S>>;

#[cfg(feature = "r1cs")]
pub mod constraints;

/// An accumulation scheme based on the hardness of the discrete log problem.
/// The construction for the accumulation scheme is taken from [[BCMS20]][pcdas].
///
/// [pcdas]: https://eprint.iacr.org/2020/499
pub struct DLAccumulationScheme<G, P, D, R, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    P: UVPolynomial<G::ScalarField>,
    D: Digest,
    R: RngCore + SeedableRng,
    CF: PrimeField + Absorbable<CF>,
    Vec<CF>: Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    _curve: PhantomData<G>,
    _polynomial: PhantomData<P>,
    _digest: PhantomData<D>,
    _rng: PhantomData<R>,
    _constraint_field: PhantomData<CF>,
    _sponge: PhantomData<S>,
}

impl<G, P, D, R, CF, S> DLAccumulationScheme<G, P, D, R, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    P: UVPolynomial<G::ScalarField>,
    D: Digest,
    R: RngCore + SeedableRng,
    CF: PrimeField + Absorbable<CF>,
    Vec<CF>: Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    fn deterministic_commit_to_linear_polynomial(
        ck: &ipa_pc::CommitterKey<G>,
        linear_polynomial: P,
    ) -> Result<FinalCommKey<G>, PCError> {
        assert!(linear_polynomial.degree() <= 1);

        let labeled_random_linear_polynomial =
            LabeledPolynomial::new(PolynomialLabel::new(), linear_polynomial, None, None);

        let (mut linear_polynomial_commitments, _) =
            PCDL::<G, P, D, CF, S>::commit(ck, vec![&labeled_random_linear_polynomial], None)?;

        Ok(linear_polynomial_commitments
            .pop()
            .unwrap()
            .commitment()
            .comm)
    }

    fn succinct_check_inputs<'a>(
        ipa_vk: &ipa_pc::VerifierKey<G>,
        inputs: impl IntoIterator<Item = &'a InputInstance<G>>,
        inputs_are_accumulators: bool, // For error handling
        output: &mut Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>,
    ) -> Result<(), ASError> {
        for input in inputs {
            let ipa_commitment = &input.ipa_commitment;
            if ipa_commitment.degree_bound().is_some() {
                return Err(if inputs_are_accumulators {
                    ASError::MalformedAccumulator(
                        "Explicit degree bounds not supported in accumulators".to_string(),
                    )
                } else {
                    ASError::MalformedInput(
                        "Explicit degree bounds not supported in inputs".to_string(),
                    )
                });
            }

            let check_polynomial = PCDL::<G, P, D, CF, S>::succinct_check(
                ipa_vk,
                vec![ipa_commitment],
                input.point.clone(),
                vec![input.evaluation],
                &input.ipa_proof,
                &|_| G::ScalarField::one(),
            );

            if check_polynomial.is_none() {
                return Err(if inputs_are_accumulators {
                    ASError::MalformedAccumulator(
                        "Succinct check failed on accumulator".to_string(),
                    )
                } else {
                    ASError::MalformedInput("Succinct check failed on input".to_string())
                });
            }

            output.push((check_polynomial.unwrap(), input.ipa_proof.final_comm_key));
        }

        Ok(())
    }

    fn succinct_check_inputs_and_accumulators<'a>(
        ipa_vk: &ipa_pc::VerifierKey<G>,
        inputs: impl IntoIterator<Item = &'a InputInstance<G>>,
        accumulators: impl IntoIterator<Item = &'a InputInstance<G>>,
    ) -> Result<Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>, ASError> {
        let mut output: Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)> =
            Vec::new();
        Self::succinct_check_inputs(ipa_vk, inputs, false, &mut output)?;
        Self::succinct_check_inputs(ipa_vk, accumulators, true, &mut output)?;
        if output.len() == 0 {
            return Err(ASError::MissingAccumulatorsAndInputs(
                "Nothing to accumulate".to_string(),
            ));
        }
        Ok(output)
    }

    fn absorb_check_polynomial_into_sponge(
        sponge: &mut impl CryptographicSponge<CF>,
        check_polynomial: &SuccinctCheckPolynomial<G::ScalarField>,
        log_supported_degree: usize,
    ) {
        assert!(check_polynomial.0.len() <= log_supported_degree);
        let mut bytes_input = Vec::new();

        let elems = &check_polynomial.0;
        // TODO: Absorb field elements instead?
        for i in 0..(log_supported_degree + 1) {
            if i < elems.len() {
                bytes_input.append(&mut ark_ff::to_bytes!(elems[i]).unwrap());
            } else {
                // Pad the check polynomial if necessary
                bytes_input.append(&mut ark_ff::to_bytes!(G::ScalarField::zero()).unwrap());
            }
        }

        sponge.absorb(&bytes_input);
    }

    fn combine_succinct_checks_and_proof<'a>(
        ipa_vk: &ipa_pc::VerifierKey<G>,
        succinct_checks: &'a Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>,
        proof: &Proof<G, P>,
    ) -> Result<
        (
            LabeledCommitment<ipa_pc::Commitment<G>>, // Combined commitment
            Vec<(G::ScalarField, &'a SuccinctCheckPolynomial<G::ScalarField>)>, // Addends to compute combined check polynomial
            G::ScalarField, // New challenge point
        ),
        ASError,
    > {
        let supported_degree = ipa_vk.supported_degree();
        let log_supported_degree = ark_std::log2(supported_degree + 1) as usize;

        assert!(proof.random_linear_polynomial.degree() <= 1);
        let mut linear_combination_challenge_sponge = SpongeForAccScheme::<CF, S>::new();
        // TODO: Renable for hiding
        /*
        let random_coeffs = proof.random_linear_polynomial.coeffs();
        for i in 0..=1 {
            if i < random_coeffs.len() {
                linear_combination_challenge_sponge.absorb(&random_coeffs[i]);
            } else {
                linear_combination_challenge_sponge.absorb(&G::ScalarField::zero());
            }
        }
         */

        /*
        linear_combination_challenge_sponge
            .absorb(&to_bytes!(proof.random_linear_polynomial_commitment).unwrap());
         */

        for (check_polynomial, commitment) in succinct_checks {
            Self::absorb_check_polynomial_into_sponge(
                &mut linear_combination_challenge_sponge,
                check_polynomial,
                log_supported_degree,
            );
            linear_combination_challenge_sponge.absorb(&commitment.to_field_elements().unwrap());
        }

        let linear_combination_challenges: Vec<G::ScalarField> =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated { num_bits: 128 }; succinct_checks.len()]
                    .as_slice(),
            );

        // TODO: Revert to enable hiding
        //let mut combined_commitment = proof.random_linear_polynomial_commitment.into_projective();
        let mut combined_commitment = G::Projective::zero();
        let mut combined_check_polynomial_addends = Vec::with_capacity(succinct_checks.len());

        for ((check_polynomial, commitment), cur_challenge) in
            succinct_checks.iter().zip(linear_combination_challenges)
        {
            combined_commitment += &(commitment.mul(cur_challenge));
            combined_check_polynomial_addends.push((cur_challenge, check_polynomial));
        }

        // TODO: Revert to enable hiding
        let randomized_combined_commitment = combined_commitment; //+ &(ipa_vk.s.mul(proof.commitment_randomness));

        let mut commitments = G::Projective::batch_normalization_into_affine(&[
            combined_commitment,
            randomized_combined_commitment,
        ]);

        let randomized_combined_commitment = commitments.pop().unwrap();
        let randomized_combined_ipa_commitment = LabeledCommitment::new(
            PolynomialLabel::new(),
            ipa_pc::Commitment {
                comm: randomized_combined_commitment,
                shifted_comm: None,
            },
            None,
        );

        let mut challenge_point_sponge = SpongeForAccScheme::<CF, S>::new();

        let combined_commitment = commitments.pop().unwrap();
        challenge_point_sponge.absorb(&combined_commitment.to_field_elements().unwrap());

        for (linear_combination_challenge, check_polynomial) in &combined_check_polynomial_addends {
            let mut linear_combination_challenge_bytes =
                to_bytes!(linear_combination_challenge).unwrap();
            linear_combination_challenge_bytes.resize_with(16, || 0);
            challenge_point_sponge.absorb(&linear_combination_challenge_bytes);

            Self::absorb_check_polynomial_into_sponge(
                &mut challenge_point_sponge,
                check_polynomial,
                log_supported_degree,
            );
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])
            .pop()
            .unwrap();

        Ok((
            randomized_combined_ipa_commitment,
            combined_check_polynomial_addends,
            challenge_point,
        ))
    }

    fn combine_check_polynomials<'a>(
        combined_check_polynomial_addends: impl IntoIterator<
            Item = (G::ScalarField, &'a SuccinctCheckPolynomial<G::ScalarField>),
        >,
    ) -> P {
        let mut combined = P::zero();
        for (scalar, check_polynomial) in combined_check_polynomial_addends {
            let polynomial = P::from_coefficients_vec(check_polynomial.compute_coeffs());
            combined += (scalar, &polynomial);
        }
        combined
    }

    fn evaluate_combined_check_polynomials<'a>(
        combined_check_polynomial_addends: impl IntoIterator<
            Item = (G::ScalarField, &'a SuccinctCheckPolynomial<G::ScalarField>),
        >,
        point: G::ScalarField,
    ) -> G::ScalarField {
        let mut eval = G::ScalarField::zero();
        for (scalar, polynomial) in combined_check_polynomial_addends {
            eval += &polynomial.evaluate(point).mul(&scalar);
        }
        eval
    }

    fn compute_new_accumulator(
        ipa_ck: &ipa_pc::CommitterKey<G>,
        combined_check_polynomial: P,
        combined_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,
        challenge: G::ScalarField,
        commitment_randomness: G::ScalarField,
        rng: &mut dyn RngCore,
    ) -> Result<InputInstance<G>, PCError> {
        let supported_degree = ipa_ck.supported_degree();
        assert!(combined_check_polynomial.degree() <= supported_degree);

        let evaluation = combined_check_polynomial.evaluate(&challenge);
        let labeled_combined_polynomial = LabeledPolynomial::new(
            PolynomialLabel::new(),
            combined_check_polynomial,
            None,
            // TODO: Turn on hiding again
            None,
        );

        let randomness = ipa_pc::Randomness {
            rand: commitment_randomness,
            shifted_rand: None,
        };

        let ipa_proof = PCDL::<G, P, D, CF, S>::open_individual_opening_challenges(
            ipa_ck,
            vec![&labeled_combined_polynomial],
            vec![&combined_commitment],
            &challenge,
            &|_| G::ScalarField::one(),
            vec![&randomness],
            Some(rng),
        )?;

        let accumulator = InputInstance {
            ipa_commitment: combined_commitment,
            point: challenge,
            evaluation,
            ipa_proof,
        };

        Ok(accumulator)
    }
}

impl<G, P, D, R, CF, S> AidedAccumulationScheme for DLAccumulationScheme<G, P, D, R, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    P: UVPolynomial<G::ScalarField>,
    D: Digest,
    R: RngCore + SeedableRng,
    CF: PrimeField + Absorbable<CF>,
    Vec<CF>: Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    type UniversalParams = ();
    type PredicateParams = ipa_pc::UniversalParams<G>;

    type PredicateIndex = PredicateIndex;
    type ProverKey = ProverKey<G>;
    type VerifierKey = VerifierKey<G>;
    type DeciderKey = DeciderKey<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = ();

    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = ();

    type Proof = Proof<G, P>;
    type Error = BoxedError;

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ipa_ck, ipa_vk) = PCDL::<G, P, D, CF, S>::trim(
            predicate_params,
            predicate_index.supported_degree_bound,
            predicate_index.supported_hiding_bound,
            None,
        )
        .map_err(|e| BoxedError::new(e))?;

        let (ipa_ck_linear, _) = PCDL::<G, P, D, CF, S>::trim(predicate_params, 1, 0, Some(&[1]))
            .map_err(|e| BoxedError::new(e))?;

        let verifier_key = VerifierKey {
            ipa_vk,
            ipa_ck_linear,
        };

        let prover_key = ProverKey {
            ipa_ck: ipa_ck.clone(),
            verifier_key: verifier_key.clone(),
        };

        let decider_key = DeciderKey(ipa_ck);

        Ok((prover_key, verifier_key, decider_key))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, Self>>,
        accumulators: impl IntoIterator<Item = AccumulatorRef<'a, Self>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let rng = rng.expect("dl_as prover requires rng");

        let inputs = InputRef::<'a, Self>::instances(inputs);
        let accumulators = AccumulatorRef::<'a, Self>::instances(accumulators);

        let random_linear_polynomial =
            P::from_coefficients_slice(&[G::ScalarField::rand(rng), G::ScalarField::rand(rng)]);

        let linear_polynomial_commitment = Self::deterministic_commit_to_linear_polynomial(
            &prover_key.verifier_key.ipa_ck_linear,
            random_linear_polynomial.clone(),
        )
        .map_err(|e| BoxedError::new(e))?;

        let proof = Proof {
            random_linear_polynomial,
            random_linear_polynomial_commitment: linear_polynomial_commitment,
            commitment_randomness: G::ScalarField::rand(rng),
        };

        let succinct_checks = Self::succinct_check_inputs_and_accumulators(
            &prover_key.verifier_key.ipa_vk,
            inputs,
            accumulators,
        )
        .map_err(|e| BoxedError::new(e))?;

        let (combined_commitment, combined_check_polynomial_addends, challenge) =
            Self::combine_succinct_checks_and_proof(
                &prover_key.verifier_key.ipa_vk,
                &succinct_checks,
                &proof,
            )
            .map_err(|e| BoxedError::new(e))?;

        let combined_check_polynomial =
            Self::combine_check_polynomials(combined_check_polynomial_addends);

        // TODO: Reenable for hiding
        //combined_check_polynomial += &proof.random_linear_polynomial;

        let accumulator = Self::compute_new_accumulator(
            &prover_key.ipa_ck,
            combined_check_polynomial,
            combined_commitment,
            challenge,
            proof.commitment_randomness.clone(),
            rng,
        )
        .map_err(|e| BoxedError::new(e))?;

        let accumulator = Accumulator::<Self> {
            instance: accumulator,
            witness: (),
        };

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
        // TODO: Revert for hiding
        /*
        if proof.random_linear_polynomial.degree() > 1 {
            return Ok(false);
        }

        let linear_polynomial_commitment = Self::deterministic_commit_to_linear_polynomial(
            &verifier_key.ipa_ck_linear,
            proof.random_linear_polynomial.clone(),
        )
        .map_err(|e| BoxedError::new(e))?;

        if !linear_polynomial_commitment.eq(&proof.random_linear_polynomial_commitment) {
            return Ok(false);
        }

         */

        let succinct_check_result = Self::succinct_check_inputs_and_accumulators(
            &verifier_key.ipa_vk,
            inputs,
            accumulators,
        );

        if succinct_check_result.is_err() {
            return Ok(false);
        };

        let succinct_checks = succinct_check_result.ok().unwrap();

        let combine_result =
            Self::combine_succinct_checks_and_proof(&verifier_key.ipa_vk, &succinct_checks, &proof);

        if combine_result.is_err() {
            return Ok(false);
        }

        let (combined_commitment, combined_check_polynomial_addends, challenge) =
            combine_result.ok().unwrap();

        if !combined_commitment
            .commitment()
            .eq(&new_accumulator.ipa_commitment.commitment())
        {
            return Ok(false);
        }

        if !challenge.eq(&new_accumulator.point) {
            return Ok(false);
        }

        let eval =
            Self::evaluate_combined_check_polynomials(combined_check_polynomial_addends, challenge);

        // TODO: Revert for hiding
        //eval += &proof.random_linear_polynomial.evaluate(&challenge);

        if !eval.eq(&new_accumulator.evaluation) {
            return Ok(false);
        }

        Ok(true)
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<Self>,
    ) -> Result<bool, Self::Error> {
        let accumulator = accumulator.instance;

        let ipa_check = PCDL::<G, P, D, CF, S>::check_individual_opening_challenges(
            &decider_key.0,
            vec![&accumulator.ipa_commitment],
            &accumulator.point,
            vec![accumulator.evaluation],
            &accumulator.ipa_proof,
            &|_| G::ScalarField::one(),
            None,
        )
        .map_err(|e| BoxedError::new(e))?;

        Ok(ipa_check)
    }
}

impl<G, P, D, R, CF, S> AccumulationScheme for DLAccumulationScheme<G, P, D, R, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    P: UVPolynomial<G::ScalarField>,
    D: Digest,
    R: RngCore + SeedableRng,
    CF: PrimeField + Absorbable<CF>,
    Vec<CF>: Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
}

#[cfg(test)]
pub mod tests {
    use crate::dl_as::data_structures::{InputInstance, PredicateIndex};
    use crate::dl_as::{DLAccumulationScheme, Input, PCDL};
    use crate::error::BoxedError;
    use crate::tests::{
        accumulators_only_test, multiple_accumulations_multiple_inputs_test,
        multiple_accumulations_test, multiple_inputs_test, single_input_test,
        AccumulationSchemeTestInput,
    };
    use crate::AidedAccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq, Fr};
    use ark_ff::{One, PrimeField, ToConstraintField, UniformRand};
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::{ipa_pc, LabeledPolynomial, PCCommitterKey};
    use ark_poly_commit::{PolynomialCommitment, UVPolynomial};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use digest::Digest;
    use rand_core::{RngCore, SeedableRng};

    pub struct DLAccumulationSchemeTestInput {}

    impl<G, P, D, R, CF, S> AccumulationSchemeTestInput<DLAccumulationScheme<G, P, D, R, CF, S>>
        for DLAccumulationSchemeTestInput
    where
        G: AffineCurve + ToConstraintField<CF>,
        P: UVPolynomial<G::ScalarField>,
        D: Digest,
        R: RngCore + SeedableRng,
        CF: PrimeField + Absorbable<CF>,
        Vec<CF>: Absorbable<CF>,
        S: CryptographicSponge<CF>,
    {
        type TestParams = ();
        type InputParams = (ipa_pc::CommitterKey<G>, ipa_pc::VerifierKey<G>);

        fn setup(
            _test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <DLAccumulationScheme<G, P, D, R, CF, S> as AidedAccumulationScheme>::PredicateParams,
            <DLAccumulationScheme<G, P, D, R, CF, S> as AidedAccumulationScheme>::PredicateIndex,
        ) {
            let max_degree = (1 << 10) - 1;
            let supported_degree = max_degree;
            let predicate_params = PCDL::<G, P, D, CF, S>::setup(max_degree, None, rng).unwrap();

            let (ck, vk) = PCDL::<G, P, D, CF, S>::trim(
                &predicate_params,
                supported_degree,
                supported_degree,
                None,
            )
            .unwrap();

            let predicate_index = PredicateIndex {
                supported_degree_bound: supported_degree,
                supported_hiding_bound: supported_degree,
            };

            ((ck, vk), predicate_params, predicate_index)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<DLAccumulationScheme<G, P, D, R, CF, S>>> {
            let ck = &input_params.0;

            let labeled_polynomials: Vec<LabeledPolynomial<G::ScalarField, P>> = (0..num_inputs)
                .map(|i| {
                    //let degree =
                    //rand::distributions::Uniform::from(1..=ck.supported_degree()).sample(rng);
                    let degree = PCCommitterKey::supported_degree(ck);
                    let label = format!("Input{}", i);

                    let polynomial = P::rand(degree, rng);
                    //let hiding_bound = None;

                    let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, randoms) =
                PCDL::<G, P, D, CF, S>::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

            let inputs = (&labeled_polynomials)
                .into_iter()
                .zip(labeled_commitments)
                .zip(&randoms)
                .map(|((labeled_polynomial, labeled_commitment), randomness)| {
                    let point = G::ScalarField::rand(rng);
                    let evaluation = labeled_polynomial.evaluate(&point);
                    let ipa_proof = PCDL::<G, P, D, CF, S>::open_individual_opening_challenges(
                        ck,
                        vec![labeled_polynomial],
                        vec![&labeled_commitment],
                        &point,
                        &|_| G::ScalarField::one(),
                        vec![randomness],
                        Some(rng),
                    )
                    .unwrap();

                    let input = InputInstance {
                        ipa_commitment: labeled_commitment,
                        point,
                        evaluation,
                        ipa_proof,
                    };

                    Input::<DLAccumulationScheme<G, P, D, R, CF, S>> {
                        instance: input,
                        witness: (),
                    }
                })
                .collect();

            inputs
        }
    }

    type AS = DLAccumulationScheme<
        EdwardsAffine,
        DensePolynomial<Fr>,
        sha2::Sha512,
        rand_chacha::ChaChaRng,
        Fq,
        PoseidonSponge<Fq>,
    >;
    type I = DLAccumulationSchemeTestInput;

    #[test]
    pub fn dl_single_input_test() -> Result<(), BoxedError> {
        single_input_test::<AS, I>(&())
    }

    #[test]
    pub fn dl_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_inputs_test::<AS, I>(&())
    }

    #[test]
    pub fn dl_multiple_accumulations_test() -> Result<(), BoxedError> {
        multiple_accumulations_test::<AS, I>(&())
    }

    #[test]
    pub fn dl_multiple_accumulations_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_accumulations_multiple_inputs_test::<AS, I>(&())
    }

    #[test]
    pub fn dl_accumulators_only_test() -> Result<(), BoxedError> {
        accumulators_only_test::<AS, I>(&())
    }
}
