use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::ConstraintF;
use crate::{AccumulationScheme, MakeZK};

use ark_ec::AffineCurve;
use ark_ff::{to_bytes, One, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::trivial_pc::TrivialPC;
use ark_poly_commit::{
    trivial_pc, Error as PCError, LabeledCommitment, LabeledPolynomial, PCCommitterKey,
    PolynomialCommitment, PolynomialLabel, UVPolynomial,
};
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::format;
use ark_std::marker::PhantomData;
use ark_std::ops::{Add, Div, Mul};
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

/// The verifier constraints of [`ASForTrivialPC`].
#[cfg(feature = "r1cs")]
pub mod constraints;

/// An accumulation scheme for a trivial homomorphic commitment schemes.
/// This implementation is specialized for [`TrivialPC`][trivial-pc].
/// The construction is described in detail in Section 7 of [\[BCLMS20\]][bclms20].
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 10.1 in [\[BCLMS20\]][bclms20] for more details.
///
/// [trivial-pc]: ark_poly_commit::trivial_pc::TrivialPC
/// [bclms20]: https://eprint.iacr.org/2020/1618
///
/// # Example Input
/// ```
///
/// use ark_accumulation::trivial_pc_as::{ASForTrivialPC, InputInstance};
/// use ark_accumulation::Input;
/// use ark_ec::AffineCurve;
/// use ark_ff::Field;
/// use ark_poly::univariate::DensePolynomial;
/// use ark_poly_commit::{trivial_pc, LabeledCommitment, LabeledPolynomial};
/// use ark_sponge::Absorbable;
///
/// type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
///
/// // An accumulation input for this scheme is formed from:
/// // 1. A TrivialPC commitment to a polynomial:            `comm`
/// // 2. A point where the polynomial will be evaluated at: `point`
/// // 3. The evaluation of the polynomial at the point:     `eval`
/// // 4. The TrivialPC opening proof:                       `proof`
/// fn new_accumulation_input<G>(
///     comm: LabeledCommitment<trivial_pc::Commitment<G>>,
///     point: G::ScalarField,
///     eval: G::ScalarField,
///     proof: trivial_pc::Proof<G::ScalarField, DensePolynomial<G::ScalarField>>,
/// ) -> Input<ConstraintF<G>, ASForTrivialPC<G>>
///     where
///         G: AffineCurve + Absorbable<ConstraintF<G>>,
///         ConstraintF<G>: Absorbable<ConstraintF<G>>
/// {
///     let instance = InputInstance {
///         commitment: comm,
///         point,
///         eval,
///     };
///
///     let witness = proof.polynomial;
///
///     Input::<_, ASForTrivialPC<G>> { instance, witness }
/// }
/// ```
pub struct ASForTrivialPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    _curve: PhantomData<G>,
}

impl<G> ASForTrivialPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    /// Check that the input instance is properly structured.
    fn check_input_instance_structure(
        instance: &InputInstance<G>,
        is_accumulator: bool,
    ) -> Result<&InputInstance<G>, BoxedError> {
        // Accumulating commitments with degree bounds are unsupported.
        if instance.commitment.degree_bound().is_some() {
            if is_accumulator {
                return Err(BoxedError::new(ASError::MalformedAccumulator(
                    "Degree bounds on accumulator instances are unsupported.".to_string(),
                )));
            }

            return Err(BoxedError::new(ASError::MalformedInput(
                "Degree bounds on input instances are unsupported.".to_string(),
            )));
        }

        Ok(instance)
    }

    /// Check that the input witness is properly structured.
    fn check_input_witness_structure<'a>(
        witness: &'a LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        prover_key: &trivial_pc::CommitterKey<G>,
        is_accumulator: bool,
    ) -> Result<&'a LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>, BoxedError>
    {
        // Accumulating polynomials with degree bounds are unsupported.
        if witness.degree_bound().is_some() {
            if is_accumulator {
                return Err(BoxedError::new(ASError::MalformedAccumulator(
                    "Degree bounds on accumulator witnesses are unsupported.".to_string(),
                )));
            }

            return Err(BoxedError::new(ASError::MalformedInput(
                "Degree bounds on input witnesses are unsupported.".to_string(),
            )));
        }

        // Accumulating polynomials with hiding bounds are unsupported.
        if witness.hiding_bound().is_some() {
            if is_accumulator {
                return Err(BoxedError::new(ASError::MalformedAccumulator(
                    "Hiding bounds on accumulator witnesses are unsupported.".to_string(),
                )));
            }

            return Err(BoxedError::new(ASError::MalformedInput(
                "Hiding bounds on input witnesses are unsupported.".to_string(),
            )));
        }

        // The polynomial to be accumulated must have a degree that is supported by the prover key.
        if witness.degree() < 1 || witness.degree() > prover_key.supported_degree() {
            if is_accumulator {
                return Err(BoxedError::new(ASError::MalformedAccumulator(format!(
                    "An accumulator witness of degree {} is unsupported for this prover key",
                    witness.degree()
                ))));
            }

            return Err(BoxedError::new(ASError::MalformedInput(format!(
                "An input witness of degree {} is unsupported for this prover key",
                witness.degree()
            ))));
        }

        Ok(witness)
    }

    /// Check that the proof is properly structured.
    fn check_proof_structure(proof: &Proof<G>, num_inputs: usize) -> bool {
        // Each proof must correspond to an input.
        return proof.len() == num_inputs;
    }

    /// Compute the witness polynomials and witness commitments from the inputs.
    /// For a claim (p, z, v), the witness polynomial is w(X) = (p(X) - v)/(X - z).
    fn compute_witness_polynomials_and_commitments<'a>(
        ck: &trivial_pc::CommitterKey<G>,
        inputs: impl IntoIterator<Item = &'a InputRef<'a, ConstraintF<G>, Self>>,
    ) -> Result<
        (
            Vec<LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>>,
            Vec<LabeledCommitment<trivial_pc::Commitment<G>>>,
        ),
        PCError,
    > {
        let mut witness_polynomials = Vec::new();
        let mut witness_commitments = Vec::new();

        for input in inputs.into_iter() {
            let point = input.instance.point;
            let eval = input.instance.eval;

            let numerator = (&DensePolynomial::from_coefficients_vec(vec![-eval]))
                .add(input.witness.polynomial());
            let denominator =
                DensePolynomial::from_coefficients_vec(vec![-point, G::ScalarField::one()]);
            let witness_polynomial = (&numerator).div(&denominator);

            let labeled_witness_polynomial = LabeledPolynomial::new(
                PolynomialLabel::new(),
                witness_polynomial.clone(),
                None,
                None,
            );

            let mut witness_commitment =
                TrivialPC::commit(ck, vec![&labeled_witness_polynomial], None)?.0.pop().unwrap();

            witness_polynomials.push(labeled_witness_polynomial);
            witness_commitments.push(witness_commitment);
        }

        Ok((witness_polynomials, witness_commitments))
    }

    /// Compute the linear combination of polynomials p = \sum challenge_i * p_i.
    fn combine_polynomials<'a>(
        labeled_polynomials: impl IntoIterator<
            Item = &'a LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        >,
        challenges: &[G::ScalarField],
    ) -> DensePolynomial<G::ScalarField> {
        let mut combined_polynomial = DensePolynomial::zero();
        for (i, p) in labeled_polynomials.into_iter().enumerate() {
            combined_polynomial += (challenges[i], p.polynomial());
        }

        combined_polynomial
    }

    /// Compute the linear combination of evaluations v = \sum challenge_i * v_i.
    fn combine_evaluations<'a>(
        evaluations: impl IntoIterator<Item = &'a G::ScalarField>,
        challenges: &[G::ScalarField],
    ) -> G::ScalarField {
        let mut combined_eval = G::ScalarField::zero();
        for (i, eval) in evaluations.into_iter().enumerate() {
            combined_eval += &eval.mul(&challenges[i]);
        }

        combined_eval
    }

    /// Compute the linear combination of commitments C = \sum challenge_i * C_i.
    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<trivial_pc::Commitment<G>>>,
        challenges: &[G::ScalarField],
    ) -> trivial_pc::Commitment<G> {
        let mut scalar_commitment_pairs = Vec::new();
        for (i, c) in commitments.into_iter().enumerate() {
            scalar_commitment_pairs.push((challenges[i], c.commitment().clone()));
        }

        scalar_commitment_pairs.into_iter().sum()
    }
}

impl<G> AccumulationScheme<ConstraintF<G>> for ASForTrivialPC<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    type PublicParameters = ();
    type PredicateParams = trivial_pc::UniversalParams<G>;
    type PredicateIndex = usize;

    type ProverKey = trivial_pc::CommitterKey<G>;
    type VerifierKey = usize;
    type DeciderKey = trivial_pc::CommitterKey<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>;

    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>;

    type Proof = Proof<G>;

    type Error = BoxedError;

    fn setup(_rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error> {
        Ok(())
    }

    fn index(
        _public_params: &Self::PublicParameters,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ck, vk) = TrivialPC::<G, DensePolynomial<G::ScalarField>>::trim(
            predicate_params,
            *predicate_index,
            0,
            None,
        )
        .map_err(|e| BoxedError::new(e))?;

        Ok((ck, *predicate_index, vk))
    }

    fn prove<'a, S: CryptographicSponge<ConstraintF<G>>>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, Self>>,
        _make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<ConstraintF<G>, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let inputs: Vec<InputRef<'a, _, Self>> = inputs.into_iter().collect();
        let accumulators: Vec<AccumulatorRef<'a, _, Self>> = old_accumulators.into_iter().collect();

        let input_instances = inputs
            .iter()
            .map(|input| Self::check_input_instance_structure(input.instance, false))
            .chain(accumulators.iter().map(|accumulator| {
                Self::check_input_instance_structure(accumulator.instance, true)
            }))
            .collect::<Result<Vec<_>, BoxedError>>()?;

        let input_witnesses = inputs
            .iter()
            .map(|input| Self::check_input_witness_structure(input.witness, prover_key, false))
            .chain(accumulators.iter().map(|accumulator| {
                Self::check_input_witness_structure(accumulator.witness, prover_key, true)
            }))
            .collect::<Result<Vec<_>, BoxedError>>()?;

        if input_instances.len() == 0 {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate.".to_string(),
            )));
        }

        // Steps 1c-1d of the scheme's accumulation prover, as detailed in BCLMS20.
        let (witness_polynomials, witness_commitments) =
            Self::compute_witness_polynomials_and_commitments(
                &prover_key,
                inputs.iter().chain(&accumulators),
            )
            .map_err(|e| BoxedError::new(e))?;

        assert_eq!(input_witnesses.len(), witness_polynomials.len());
        assert_eq!(input_witnesses.len(), witness_commitments.len());

        // Step 2 of the scheme's accumulation prover, as detailed in BCLMS20.
        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(&prover_key.supported_degree());

        for (instance, witness_commitment) in input_instances.iter().zip(&witness_commitments) {
            absorb![
                &mut challenge_point_sponge,
                instance,
                witness_commitment.commitment().elem
            ];
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])
            .pop()
            .unwrap();

        let mut linear_combination_challenges_sponge = sponge;
        let mut challenge_point_bytes = to_bytes!(challenge_point).unwrap();
        challenge_point_bytes.resize_with(23, || 0u8);
        linear_combination_challenges_sponge.absorb(&challenge_point_bytes);

        let mut proof = Vec::new();
        for ((input_witness, witness_polynomial), witness_commitment) in input_witnesses
            .iter()
            .zip(&witness_polynomials)
            .zip(&witness_commitments)
        {
            // Step 3 of the scheme's accumulation prover, as detailed in BCLMS20.
            let input_witness_eval = input_witness.evaluate(&challenge_point);
            let witness_eval = witness_polynomial.evaluate(&challenge_point);

            // Step 4 of the scheme's accumulation prover, as detailed in BCLMS20.
            absorb![
                &mut linear_combination_challenges_sponge,
                &to_bytes!(&input_witness_eval).unwrap(),
                &to_bytes!(&witness_eval).unwrap()
            ];

            let single_proof = SingleProof {
                witness_commitment: witness_commitment.clone(),
                witness_eval,
                eval: input_witness_eval,
            };

            proof.push(single_proof);
        }

        // Step 4 of the scheme's accumulation prover, as detailed in BCLMS20.
        let linear_combination_challenges = linear_combination_challenges_sponge
            .squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); proof.len() * 2].as_slice(),
            );

        // Step 5 of the scheme's accumulation prover, as detailed in BCLMS20.
        let combined_polynomial = Self::combine_polynomials(
            input_witnesses.into_iter().chain(&witness_polynomials),
            linear_combination_challenges.as_slice(),
        );

        let combined_polynomial =
            LabeledPolynomial::new(PolynomialLabel::new(), combined_polynomial, None, None);

        // Step 6 of the scheme's accumulation prover, as detailed in BCLMS20.
        let combined_eval = combined_polynomial.evaluate(&challenge_point);

        // Step 7 of the scheme's accumulation prover, as detailed in BCLMS20.
        let combined_commitment = Self::combine_commitments(
            input_instances
                .into_iter()
                .map(|instance| &instance.commitment)
                .chain(&witness_commitments),
            linear_combination_challenges.as_slice(),
        );

        let combined_commitment =
            LabeledCommitment::new(PolynomialLabel::new(), combined_commitment, None);

        // Step 8-10 of the scheme's accumulation prover, as detailed in BCLMS20.
        let new_accumulator_instance = InputInstance {
            commitment: combined_commitment,
            point: challenge_point,
            eval: combined_eval,
        };

        let new_accumulator = Accumulator::<_, Self> {
            instance: new_accumulator_instance,
            witness: combined_polynomial,
        };

        Ok((new_accumulator, proof))
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
        let sponge = sponge.unwrap_or_else(|| S::new());

        // Collect the input and run basic checks on them.
        let input_instances = input_instances
            .into_iter()
            .map(|instance| Self::check_input_instance_structure(instance, false))
            .chain(
                old_accumulator_instances
                    .into_iter()
                    .map(|instance| Self::check_input_instance_structure(instance, true)),
            )
            .collect::<Result<Vec<_>, BoxedError>>();

        if input_instances.is_err() {
            return Ok(false);
        }

        let input_instances = input_instances.unwrap();
        if input_instances.len() == 0 {
            return Ok(false);
        }

        let new_accumulator_instance =
            Self::check_input_instance_structure(new_accumulator_instance, true);
        if new_accumulator_instance.is_err() {
            return Ok(false);
        }

        let new_accumulator_instance = new_accumulator_instance.unwrap();
        if input_instances.len() == 0 {
            return Ok(false);
        }

        if !Self::check_proof_structure(proof, input_instances.len()) {
            return Ok(false);
        }

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(verifier_key);

        let mut commitments = Vec::new();
        for (input_instance, p) in input_instances.into_iter().zip(proof) {
            // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
            absorb![
                &mut challenge_point_sponge,
                input_instance,
                p.witness_commitment.commitment().elem
            ];

            // Step 4 of the scheme's accumulation verifier, as detailed in BCLMS20.
            let eval_check_lhs = p.eval - &input_instance.eval;
            let eval_check_rhs = p
                .witness_eval
                .mul(&(new_accumulator_instance.point - &input_instance.point));

            if !eval_check_lhs.eq(&eval_check_rhs) {
                return Ok(false);
            }

            commitments.push(&input_instance.commitment);
        }

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let challenge_point: G::ScalarField = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])
            .pop()
            .unwrap();

        if !challenge_point.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

        // Step 5 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let mut linear_combination_challenges_sponge = sponge;
        let mut challenge_point_bytes = to_bytes!(challenge_point).unwrap();
        challenge_point_bytes.resize_with(23, || 0u8);
        linear_combination_challenges_sponge.absorb(&challenge_point_bytes);

        for single_proof in proof {
            absorb![
                &mut linear_combination_challenges_sponge,
                &to_bytes!(&single_proof.eval).unwrap(),
                &to_bytes!(&single_proof.witness_eval).unwrap()
            ];
        }

        let linear_combination_challenges = linear_combination_challenges_sponge
            .squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); proof.len() * 2].as_slice(),
            );

        // Step 6 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let combined_eval = Self::combine_evaluations(
            proof
                .into_iter()
                .map(|p| &p.eval)
                .chain(proof.into_iter().map(|p| &p.witness_eval)),
            linear_combination_challenges.as_slice(),
        );

        if !combined_eval.eq(&new_accumulator_instance.eval) {
            return Ok(false);
        }

        // Step 7 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let combined_commitment = Self::combine_commitments(
            commitments
                .into_iter()
                .chain(proof.into_iter().map(|p| &p.witness_commitment)),
            linear_combination_challenges.as_slice(),
        );

        if !combined_commitment.eq(new_accumulator_instance.commitment.commitment()) {
            return Ok(false);
        }

        Ok(true)
    }

    fn decide<'a, S: CryptographicSponge<ConstraintF<G>>>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, Self>,
        _sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let check = TrivialPC::check_individual_opening_challenges(
            decider_key,
            vec![&accumulator.instance.commitment],
            &accumulator.instance.point,
            vec![accumulator.instance.eval],
            &trivial_pc::Proof {
                polynomial: accumulator.witness.clone(),
            },
            &|_| G::ScalarField::one(),
            None,
        );

        Ok(check.is_ok() && check.ok().unwrap())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::tests::*;
    use crate::trivial_pc_as::{ASForTrivialPC, InputInstance};
    use crate::AccumulationScheme;
    use crate::ConstraintF;
    use ark_ec::AffineCurve;
    use ark_ff::ToConstraintField;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::trivial_pc::TrivialPC;
    use ark_poly_commit::{
        trivial_pc, LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial,
    };
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::Absorbable;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct ASForTrivialPCTestParams {
        pub(crate) degree: usize,
    }

    impl TestParameters for ASForTrivialPCTestParams {
        fn make_zk(&self) -> bool {
            false
        }
    }

    pub struct ASForTrivialPCTestInput {}

    impl<G> ASTestInput<ConstraintF<G>, ASForTrivialPC<G>> for ASForTrivialPCTestInput
    where
        G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
    {
        type TestParams = ASForTrivialPCTestParams;
        type InputParams = trivial_pc::CommitterKey<G>;

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <ASForTrivialPC<G> as AccumulationScheme<ConstraintF<G>>>::PredicateParams,
            <ASForTrivialPC<G> as AccumulationScheme<ConstraintF<G>>>::PredicateIndex,
        ) {
            let max_degree = test_params.degree;
            let supported_degree = max_degree;
            let supported_hiding_bound = 0;

            let predicate_params =
                TrivialPC::<G, DensePolynomial<G::ScalarField>>::setup(max_degree, None, rng)
                    .unwrap();

            let (ck, _) = TrivialPC::<G, DensePolynomial<G::ScalarField>>::trim(
                &predicate_params,
                supported_degree,
                supported_hiding_bound,
                None,
            )
            .unwrap();

            (ck, predicate_params, supported_degree)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<ConstraintF<G>, ASForTrivialPC<G>>> {
            let ck = input_params;
            let degree = PCCommitterKey::supported_degree(ck);

            let labeled_polynomials: Vec<
                LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
            > = (0..num_inputs)
                .map(|i| {
                    let label = format!("Input{}", i);

                    let polynomial = DensePolynomial::rand(degree, rng);
                    let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, _) = TrivialPC::<G, DensePolynomial<G::ScalarField>>::commit(
                ck,
                &labeled_polynomials,
                Some(rng),
            )
            .unwrap();

            let inputs = labeled_polynomials
                .into_iter()
                .zip(labeled_commitments)
                .map(|(labeled_polynomial, labeled_commitment)| {
                    let point = G::ScalarField::rand(rng);
                    let eval = labeled_polynomial.evaluate(&point);

                    let instance = InputInstance {
                        commitment: labeled_commitment,
                        point,
                        eval,
                    };

                    Input::<_, ASForTrivialPC<G>> {
                        instance,
                        witness: labeled_polynomial,
                    }
                })
                .collect();

            inputs
        }
    }

    type G = ark_pallas::Affine;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = ASForTrivialPC<G>;
    type I = ASForTrivialPCTestInput;

    type Tests = ASTests<CF, AS, I, Sponge>;

    #[test]
    pub fn single_input_init_test() -> Result<(), BoxedError> {
        Tests::single_input_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn multiple_inputs_init_test() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn simple_accumulation_test() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn multiple_inputs_accumulation_test() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn accumulators_only_test() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&ASForTrivialPCTestParams { degree: 11 })
    }

    #[test]
    pub fn no_inputs_init_test() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(&ASForTrivialPCTestParams { degree: 11 })
    }
}
