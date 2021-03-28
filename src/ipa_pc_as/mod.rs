use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::ConstraintF;
use crate::{AccumulationScheme, AtomicAccumulationScheme, MakeZK};

use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{to_bytes, One, UniformRand, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly::{Polynomial, UVPolynomial};
use ark_poly_commit::ipa_pc::{InnerProductArgPC, SuccinctCheckPolynomial};
use ark_poly_commit::{
    ipa_pc, Error as PCError, LabeledCommitment, LabeledPolynomial, PCVerifierKey,
    PolynomialCommitment, PolynomialLabel,
};
use ark_sponge::domain_separated::DomainSeparatedSponge;
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;
use blake2::Blake2s;
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

/// The verifier constraints of [`AtomicASForInnerProductArgPC`].
#[cfg(feature = "r1cs")]
pub mod constraints;

type FinalCommKey<G> = G;
type IpaPC<G, S> = InnerProductArgPC<
    G,
    Blake2s,
    DensePolynomial<<G as AffineCurve>::ScalarField>,
    ConstraintF<G>,
    DomainSeparatedSponge<ConstraintF<G>, S, IpaPCDomain>,
>;

/// An accumulation scheme for a polynomial commitment scheme based on inner product arguments.
/// This implementation is specialized for [`InnerProductArgPC`][ipa-pc].
/// The construction is described in detail in Section 7 of [BCMS20][bcms20].
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 10.1 in [BCLMS20][bclms20] for more details.
///
/// [ipa-pc]: ark_poly_commit::ipa_pc::InnerProductArgPC
/// [bcms20]: https://eprint.iacr.org/2020/499
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
pub struct AtomicASForInnerProductArgPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    _curve: PhantomData<G>,
}

impl<G> AtomicASForInnerProductArgPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    fn check_input_instance_structure(
        instance: &InputInstance<G>,
        is_accumulator: bool,
    ) -> Result<&InputInstance<G>, BoxedError> {
        let ipa_commitment = &instance.ipa_commitment;

        // Accumulating commitments with degree bounds are unsupported.
        if ipa_commitment.degree_bound().is_some() {
            return Err(BoxedError::new(if is_accumulator {
                ASError::MalformedAccumulator(
                    "Explicit degree bounds not supported in accumulators.".to_string(),
                )
            } else {
                ASError::MalformedInput(
                    "Explicit degree bounds not supported in inputs.".to_string(),
                )
            }));
        }

        Ok(instance)
    }

    fn check_proof_structure(proof: &Option<Randomness<G>>) -> bool {
        // The random polynomial in the proof must be linear.
        if let Some(randomness) = proof.as_ref() {
            return randomness.random_linear_polynomial.degree() <= 1;
        }

        return true;
    }

    fn deterministic_commit_to_linear_polynomial<S: CryptographicSponge<ConstraintF<G>>>(
        ck: &ipa_pc::CommitterKey<G>,
        linear_polynomial: DensePolynomial<G::ScalarField>,
    ) -> Result<FinalCommKey<G>, PCError> {
        let labeled_random_linear_polynomial =
            LabeledPolynomial::new(PolynomialLabel::new(), linear_polynomial, None, None);

        let (mut linear_polynomial_commitments, _) =
            IpaPC::<G, S>::commit(ck, vec![&labeled_random_linear_polynomial], None)?;

        Ok(linear_polynomial_commitments
            .pop()
            .unwrap()
            .commitment()
            .comm)
    }

    fn generate_prover_randomness<S: CryptographicSponge<ConstraintF<G>>>(
        prover_key: &ProverKey<G>,
        rng: &mut dyn RngCore,
    ) -> Result<Randomness<G>, BoxedError> {
        let random_linear_polynomial = DensePolynomial::from_coefficients_slice(&[
            G::ScalarField::rand(rng),
            G::ScalarField::rand(rng),
        ]);

        let linear_polynomial_commitment = Self::deterministic_commit_to_linear_polynomial::<S>(
            &prover_key.verifier_key.ipa_ck_linear,
            random_linear_polynomial.clone(),
        )
        .map_err(|e| BoxedError::new(e))?;

        let commitment_randomness = G::ScalarField::rand(rng);

        Ok(Randomness {
            random_linear_polynomial,
            random_linear_polynomial_commitment: linear_polynomial_commitment,
            commitment_randomness,
        })
    }

    fn succinct_check_inputs<'a, S: CryptographicSponge<ConstraintF<G>>>(
        ipa_svk: &ipa_pc::SuccinctVerifierKey<G>,
        inputs: &Vec<&InputInstance<G>>,
        inputs_are_accumulators: bool, // For error handling
        output: &mut Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>,
    ) -> Result<(), ASError> {
        for input in inputs {
            let ipa_commitment = &input.ipa_commitment;
            let check_polynomial = IpaPC::<G, S>::succinct_check(
                ipa_svk,
                vec![ipa_commitment],
                input.point.clone(),
                vec![input.evaluation],
                &input.ipa_proof,
                &|_| G::ScalarField::one(),
            );

            if check_polynomial.is_none() {
                return Err(if inputs_are_accumulators {
                    ASError::MalformedAccumulator(
                        "Succinct check failed on accumulator.".to_string(),
                    )
                } else {
                    ASError::MalformedInput("Succinct check failed on input.".to_string())
                });
            }

            output.push((check_polynomial.unwrap(), input.ipa_proof.final_comm_key));
        }

        Ok(())
    }

    fn succinct_check_inputs_and_accumulators<'a, S: CryptographicSponge<ConstraintF<G>>>(
        ipa_svk: &ipa_pc::SuccinctVerifierKey<G>,
        inputs: &Vec<&InputInstance<G>>,
        accumulators: &Vec<&InputInstance<G>>,
    ) -> Result<Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>, ASError> {
        let mut output: Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)> =
            Vec::new();

        Self::succinct_check_inputs::<S>(ipa_svk, inputs, false, &mut output)?;
        Self::succinct_check_inputs::<S>(ipa_svk, accumulators, true, &mut output)?;

        Ok(output)
    }

    fn absorb_check_polynomial_into_sponge(
        sponge: &mut impl CryptographicSponge<ConstraintF<G>>,
        check_polynomial: &SuccinctCheckPolynomial<G::ScalarField>,
    ) {
        let mut bytes_input = Vec::new();
        for elem in &check_polynomial.0 {
            bytes_input.append(&mut ark_ff::to_bytes!(elem).unwrap());
        }

        sponge.absorb(&bytes_input);
    }

    fn combine_succinct_checks_and_proof<'a, S: CryptographicSponge<ConstraintF<G>>>(
        ipa_svk: &ipa_pc::SuccinctVerifierKey<G>,
        succinct_checks: &'a Vec<(SuccinctCheckPolynomial<G::ScalarField>, FinalCommKey<G>)>,
        proof: Option<&Randomness<G>>,
        as_sponge: DomainSeparatedSponge<ConstraintF<G>, S, ASForIpaPCDomain>,
    ) -> Result<
        (
            LabeledCommitment<ipa_pc::Commitment<G>>, // Combined commitment
            Vec<(G::ScalarField, &'a SuccinctCheckPolynomial<G::ScalarField>)>, // Addends to compute combined check polynomial
            G::ScalarField, // New challenge point
        ),
        ASError,
    > {
        let mut linear_combination_challenge_sponge = as_sponge.clone();
        if let Some(randomness) = proof.as_ref() {
            let random_coeffs = randomness.random_linear_polynomial.coeffs();
            for i in 0..=1 {
                if i < random_coeffs.len() {
                    linear_combination_challenge_sponge
                        .absorb(&to_bytes!(random_coeffs[i]).unwrap());
                } else {
                    linear_combination_challenge_sponge
                        .absorb(&to_bytes!(G::ScalarField::zero()).unwrap());
                }
            }

            linear_combination_challenge_sponge
                .absorb(&randomness.random_linear_polynomial_commitment);
        }

        for (check_polynomial, commitment) in succinct_checks {
            Self::absorb_check_polynomial_into_sponge(
                &mut linear_combination_challenge_sponge,
                check_polynomial,
            );
            linear_combination_challenge_sponge.absorb(&commitment);
        }

        let linear_combination_challenges: Vec<G::ScalarField> =
            linear_combination_challenge_sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); succinct_checks.len()].as_slice(),
            );

        let mut combined_commitment = if let Some(randomness) = proof.as_ref() {
            randomness
                .random_linear_polynomial_commitment
                .into_projective()
        } else {
            G::Projective::zero()
        };

        let mut combined_check_polynomial_addends = Vec::with_capacity(succinct_checks.len());

        for ((check_polynomial, commitment), cur_challenge) in
            succinct_checks.iter().zip(linear_combination_challenges)
        {
            combined_commitment += &(commitment.mul(cur_challenge));
            combined_check_polynomial_addends.push((cur_challenge, check_polynomial));
        }

        let randomized_combined_commitment = if let Some(randomness) = proof.as_ref() {
            combined_commitment + &ipa_svk.s.mul(randomness.commitment_randomness)
        } else {
            combined_commitment.clone()
        };

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

        let mut challenge_point_sponge = as_sponge;

        let combined_commitment = commitments.pop().unwrap();
        challenge_point_sponge.absorb(&combined_commitment);

        for (linear_combination_challenge, check_polynomial) in &combined_check_polynomial_addends {
            let mut linear_combination_challenge_bytes =
                to_bytes!(linear_combination_challenge).unwrap();
            linear_combination_challenge_bytes.resize_with(16, || 0);
            challenge_point_sponge.absorb(&linear_combination_challenge_bytes);

            Self::absorb_check_polynomial_into_sponge(
                &mut challenge_point_sponge,
                check_polynomial,
            );
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])
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
    ) -> DensePolynomial<G::ScalarField> {
        let mut combined = DensePolynomial::zero();
        for (scalar, check_polynomial) in combined_check_polynomial_addends {
            let polynomial =
                DensePolynomial::from_coefficients_vec(check_polynomial.compute_coeffs());
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

    fn compute_new_accumulator<S: CryptographicSponge<ConstraintF<G>>>(
        ipa_ck: &ipa_pc::CommitterKey<G>,
        combined_check_polynomial: DensePolynomial<G::ScalarField>,
        combined_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,
        challenge: G::ScalarField,
        proof: Option<&Randomness<G>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<InputInstance<G>, PCError> {
        let hiding_bound = if proof.is_some() {
            assert!(rng.is_some());
            Some(ipa_ck.supported_degree())
        } else {
            None
        };

        let evaluation = combined_check_polynomial.evaluate(&challenge);
        let labeled_combined_polynomial = LabeledPolynomial::new(
            PolynomialLabel::new(),
            combined_check_polynomial,
            None,
            hiding_bound,
        );

        let randomness = ipa_pc::Randomness {
            rand: proof
                .map(|rand| rand.commitment_randomness.clone())
                .unwrap_or(G::ScalarField::zero()),
            shifted_rand: None,
        };

        let ipa_proof = IpaPC::<G, S>::open_individual_opening_challenges(
            ipa_ck,
            vec![&labeled_combined_polynomial],
            vec![&combined_commitment],
            &challenge,
            &|_| G::ScalarField::one(),
            vec![&randomness],
            rng,
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

impl<G> AccumulationScheme<ConstraintF<G>> for AtomicASForInnerProductArgPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    type PublicParameters = ();
    type PredicateParams = ipa_pc::UniversalParams<G>;

    type PredicateIndex = PredicateIndex;
    type ProverKey = ProverKey<G>;
    type VerifierKey = VerifierKey<G>;
    type DeciderKey = ipa_pc::VerifierKey<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = ();

    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = ();

    type Proof = Option<Randomness<G>>;
    type Error = BoxedError;

    fn setup(_rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error> {
        Ok(())
    }

    fn index(
        _public_params: &Self::PublicParameters,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ipa_ck, ipa_vk) = IpaPC::<G, UnimplementedSponge>::trim(
            predicate_params,
            predicate_index.supported_degree_bound,
            predicate_index.supported_hiding_bound,
            None,
        )
        .map_err(|e| BoxedError::new(e))?;

        let (ipa_ck_linear, _) =
            IpaPC::<G, UnimplementedSponge>::trim(predicate_params, 1, 0, Some(&[1]))
                .map_err(|e| BoxedError::new(e))?;

        let verifier_key = VerifierKey {
            ipa_svk: ipa_vk.svk.clone(),
            ipa_ck_linear,
        };

        let prover_key = ProverKey {
            ipa_ck: ipa_ck.clone(),
            verifier_key: verifier_key.clone(),
        };

        let decider_key = ipa_vk;

        Ok((prover_key, verifier_key, decider_key))
    }

    fn prove<'a, S: CryptographicSponge<ConstraintF<G>>>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<ConstraintF<G>, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        if sponge.is_some() {
            unimplemented!(
                "ASForIpaPC is unable to accept sponge objects until IpaPC gets updated to accept them."
            );
        }

        let as_sponge = DomainSeparatedSponge::<ConstraintF<G>, S, ASForIpaPCDomain>::new();

        let input_instances: Vec<&InputInstance<G>> = InputRef::<'a, _, Self>::instances(inputs)
            .map(|instance| Self::check_input_instance_structure(instance, false))
            .collect::<Result<Vec<_>, BoxedError>>()?;

        let old_accumulator_instances: Vec<&InputInstance<G>> =
            AccumulatorRef::<'a, _, Self>::instances(old_accumulators)
                .map(|instance| Self::check_input_instance_structure(instance, true))
                .collect::<Result<Vec<_>, BoxedError>>()?;

        if input_instances.is_empty() && old_accumulator_instances.is_empty() {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate.".to_string(),
            )));
        }

        let (make_zk_enabled, mut rng) = make_zk.into_components();
        if !make_zk_enabled {
            for instance in input_instances.iter().chain(&old_accumulator_instances) {
                if instance.ipa_proof.hiding_comm.is_some() || instance.ipa_proof.rand.is_some() {
                    return Err(BoxedError::new(ASError::MissingRng(
                        "Accumulating inputs with hiding requires rng.".to_string(),
                    )));
                }
            }
        };

        let proof = if make_zk_enabled {
            // If make_zk, then rng should exist here.
            assert!(rng.is_some());

            let rng_moved = rng.unwrap();
            let proof = Self::generate_prover_randomness::<S>(prover_key, rng_moved)?;

            rng = Some(rng_moved);
            Some(proof)
        } else {
            None
        };

        let succinct_checks = Self::succinct_check_inputs_and_accumulators::<S>(
            &prover_key.verifier_key.ipa_svk,
            &input_instances,
            &old_accumulator_instances,
        )
        .map_err(|e| BoxedError::new(e))?;

        let (combined_commitment, combined_check_polynomial_addends, challenge) =
            Self::combine_succinct_checks_and_proof(
                &prover_key.verifier_key.ipa_svk,
                &succinct_checks,
                proof.as_ref(),
                as_sponge,
            )
            .map_err(|e| BoxedError::new(e))?;

        let mut combined_check_polynomial =
            Self::combine_check_polynomials(combined_check_polynomial_addends);

        if let Some(randomness) = proof.as_ref() {
            combined_check_polynomial += &randomness.random_linear_polynomial;
        }

        let accumulator = Self::compute_new_accumulator::<S>(
            &prover_key.ipa_ck,
            combined_check_polynomial,
            combined_commitment,
            challenge,
            proof.as_ref(),
            rng,
        )
        .map_err(|e| BoxedError::new(e))?;

        let accumulator = Accumulator::<_, Self> {
            instance: accumulator,
            witness: (),
        };

        Ok((accumulator, proof))
    }

    fn verify<'a, S: CryptographicSponge<ConstraintF<G>>>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        if sponge.is_some() {
            unimplemented!(
                "ASForIpaPC is unable to accept sponge objects until IpaPC gets updated to accept them."
            );
        }

        let as_sponge = DomainSeparatedSponge::<ConstraintF<G>, S, ASForIpaPCDomain>::new();

        let input_instances = input_instances
            .into_iter()
            .map(|instance| Self::check_input_instance_structure(instance, false))
            .collect::<Result<Vec<_>, BoxedError>>();

        if input_instances.is_err() {
            return Ok(false);
        }

        let input_instances = input_instances.unwrap();

        let old_accumulator_instances = old_accumulator_instances
            .into_iter()
            .map(|instance| Self::check_input_instance_structure(instance, true))
            .collect::<Result<Vec<_>, BoxedError>>();

        if old_accumulator_instances.is_err() {
            return Ok(false);
        }

        let old_accumulator_instances = old_accumulator_instances.unwrap();

        if input_instances.is_empty() && old_accumulator_instances.is_empty() {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate.".to_string(),
            )));
        }

        if !Self::check_proof_structure(&proof) {
            return Ok(false);
        }

        if let Some(randomness) = proof.as_ref() {
            let linear_polynomial_commitment =
                Self::deterministic_commit_to_linear_polynomial::<S>(
                    &verifier_key.ipa_ck_linear,
                    randomness.random_linear_polynomial.clone(),
                )
                .map_err(|e| BoxedError::new(e))?;

            if !linear_polynomial_commitment.eq(&randomness.random_linear_polynomial_commitment) {
                return Ok(false);
            }
        }

        let succinct_check_result = Self::succinct_check_inputs_and_accumulators::<S>(
            &verifier_key.ipa_svk,
            &input_instances,
            &old_accumulator_instances,
        );

        if succinct_check_result.is_err() {
            return Ok(false);
        };

        let succinct_checks = succinct_check_result.ok().unwrap();

        if succinct_checks.is_empty() {
            return Ok(false);
        }

        let combine_result = Self::combine_succinct_checks_and_proof(
            &verifier_key.ipa_svk,
            &succinct_checks,
            proof.as_ref(),
            as_sponge,
        );

        if combine_result.is_err() {
            return Ok(false);
        }

        let (combined_commitment, combined_check_polynomial_addends, challenge) =
            combine_result.ok().unwrap();

        if !combined_commitment
            .commitment()
            .eq(&new_accumulator_instance.ipa_commitment.commitment())
        {
            return Ok(false);
        }

        if !challenge.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

        let mut eval =
            Self::evaluate_combined_check_polynomials(combined_check_polynomial_addends, challenge);

        if let Some(randomness) = proof.as_ref() {
            eval += &randomness.random_linear_polynomial.evaluate(&challenge);
        }

        if !eval.eq(&new_accumulator_instance.evaluation) {
            return Ok(false);
        }

        Ok(true)
    }

    fn decide<'a, S: CryptographicSponge<ConstraintF<G>>>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, Self>,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        if sponge.is_some() {
            unimplemented!(
                "ASForIpaPC is unable to accept sponge objects until IpaPC gets updated to accept them."
            );
        }

        let accumulator = accumulator.instance;

        let ipa_check = IpaPC::<G, S>::check_individual_opening_challenges(
            decider_key,
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

impl<G> AtomicAccumulationScheme<ConstraintF<G>> for AtomicASForInnerProductArgPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::ipa_pc_as::data_structures::{InputInstance, PredicateIndex};
    use crate::ipa_pc_as::{AtomicASForInnerProductArgPC, IpaPC};
    use crate::tests::{ASTestInput, ASTests, TestParameters};
    use crate::AccumulationScheme;
    use crate::ConstraintF;
    use ark_ec::AffineCurve;
    use ark_ff::{One, PrimeField, UniformRand};
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::{ipa_pc, LabeledPolynomial, PCCommitterKey};
    use ark_poly_commit::{PolynomialCommitment, UVPolynomial};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use ark_std::marker::PhantomData;
    use ark_std::vec::Vec;
    use rand_core::RngCore;

    pub struct AtomicASForIpaPCTestParams {
        pub(crate) degree: usize,
        pub(crate) make_zk: bool,
    }

    impl TestParameters for AtomicASForIpaPCTestParams {
        fn make_zk(&self) -> bool {
            self.make_zk
        }
    }

    pub struct AtomicASForIpaPCTestInput<CF: PrimeField, S: CryptographicSponge<CF>> {
        _cf: PhantomData<CF>,
        _sponge: PhantomData<S>,
    }

    impl<G, S> ASTestInput<ConstraintF<G>, AtomicASForInnerProductArgPC<G>>
        for AtomicASForIpaPCTestInput<ConstraintF<G>, S>
    where
        G: AffineCurve + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = AtomicASForIpaPCTestParams;
        type InputParams = (ipa_pc::CommitterKey<G>, ipa_pc::VerifierKey<G>, bool);

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <AtomicASForInnerProductArgPC<G> as AccumulationScheme<ConstraintF<G>>>::PredicateParams,
            <AtomicASForInnerProductArgPC<G> as AccumulationScheme<ConstraintF<G>>>::PredicateIndex,
        ){
            let max_degree = test_params.degree;
            let supported_degree = max_degree;
            let predicate_params = IpaPC::<G, S>::setup(max_degree, None, rng).unwrap();
            let supported_hiding_bound = if test_params.make_zk {
                supported_degree
            } else {
                0
            };

            let (ck, vk) = IpaPC::<G, S>::trim(
                &predicate_params,
                supported_degree,
                supported_hiding_bound,
                None,
            )
            .unwrap();

            let predicate_index = PredicateIndex {
                supported_degree_bound: supported_degree,
                supported_hiding_bound,
            };

            (
                (ck, vk, test_params.make_zk),
                predicate_params,
                predicate_index,
            )
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<ConstraintF<G>, AtomicASForInnerProductArgPC<G>>> {
            let ck = &input_params.0;
            let degree = PCCommitterKey::supported_degree(ck);

            let make_zk = input_params.2;
            let hiding_bound = if make_zk { Some(degree) } else { None };

            let labeled_polynomials: Vec<
                LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
            > = (0..num_inputs)
                .map(|i| {
                    //let degree =
                    //rand::distributions::Uniform::from(1..=ck.supported_degree()).sample(rng);
                    let label = format!("Input{}", i);
                    let polynomial = DensePolynomial::rand(degree, rng);
                    let labeled_polynomial =
                        LabeledPolynomial::new(label, polynomial, None, hiding_bound.clone());

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, randoms) =
                IpaPC::<G, S>::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

            let inputs = (&labeled_polynomials)
                .into_iter()
                .zip(labeled_commitments)
                .zip(&randoms)
                .map(|((labeled_polynomial, labeled_commitment), randomness)| {
                    let point = G::ScalarField::rand(rng);
                    let evaluation = labeled_polynomial.evaluate(&point);
                    let ipa_proof = IpaPC::<G, S>::open_individual_opening_challenges(
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

                    Input::<_, AtomicASForInnerProductArgPC<G>> {
                        instance: input,
                        witness: (),
                    }
                })
                .collect();

            inputs
        }
    }

    type G = ark_pallas::Affine;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = AtomicASForInnerProductArgPC<G>;
    type I = AtomicASForIpaPCTestInput<CF, Sponge>;

    type Tests = ASTests<CF, AS, I, Sponge>;

    #[test]
    pub fn single_input_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_no_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&AtomicASForIpaPCTestParams {
            degree: 11,
            make_zk: true,
        })
    }
}
