use crate::constraints::ConstraintF;
use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::std::marker::PhantomData;
use crate::std::ops::{Add, Div};
use crate::std::string::ToString;
use crate::std::vec::Vec;
use crate::{AccumulationScheme, MakeZK};
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, One, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::lh_pc::LHPCError;
use ark_poly_commit::lh_pc::LinearHashPC;
use ark_poly_commit::{
    lh_pc, LabeledCommitment, LabeledPolynomial, PCCommitterKey, PolynomialCommitment,
    PolynomialLabel, UVPolynomial,
};
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use rand_core::RngCore;
use std::ops::Mul;

mod data_structures;
pub use data_structures::*;

#[cfg(feature = "r1cs")]
pub mod constraints;

pub struct HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _curve: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    fn compute_witness_polynomials_and_witnesses_from_inputs<'a>(
        ck: &lh_pc::CommitterKey<G>,
        input_instances: impl IntoIterator<Item = &'a InputInstance<G>>,
        input_witnesses: impl IntoIterator<
            Item = &'a LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        >,

        // Outputs
        witness_polynomials_output: &mut Vec<
            LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        >,
        witness_commitments_output: &mut Vec<LabeledCommitment<lh_pc::Commitment<G>>>,
    ) -> Result<(), LHPCError> {
        for (instance, witness) in input_instances.into_iter().zip(input_witnesses) {
            let point = instance.point;
            let eval = instance.eval;

            let numerator =
                (&DensePolynomial::from_coefficients_vec(vec![-eval])).add(witness.polynomial());
            let denominator =
                DensePolynomial::from_coefficients_vec(vec![-point, G::ScalarField::one()]);
            let witness_polynomial = (&numerator).div(&denominator);

            let labeled_witness_polynomial = LabeledPolynomial::new(
                PolynomialLabel::new(),
                witness_polynomial.clone(),
                None,
                None,
            );

            let mut witness_commitments =
                LinearHashPC::commit(ck, vec![&labeled_witness_polynomial], None)?.0;

            let witness_commitment = witness_commitments.pop().unwrap();

            witness_polynomials_output.push(labeled_witness_polynomial);
            witness_commitments_output.push(witness_commitment);
        }

        Ok(())
    }

    fn compute_witness_polynomials_and_commitments<'a>(
        ck: &lh_pc::CommitterKey<G>,
        inputs: &[InputRef<'a, ConstraintF<G>, S, Self>],
        accumulators: &[AccumulatorRef<'a, ConstraintF<G>, S, Self>],
    ) -> Result<
        (
            Vec<LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>>,
            Vec<LabeledCommitment<lh_pc::Commitment<G>>>,
        ),
        LHPCError,
    > {
        let mut witness_polynomials = Vec::new();
        let mut witness_commitments = Vec::new();

        let input_instances = inputs.into_iter().map(|i| i.instance);
        let input_witnesses = inputs.into_iter().map(|i| i.witness);

        Self::compute_witness_polynomials_and_witnesses_from_inputs(
            ck,
            input_instances,
            input_witnesses,
            &mut witness_polynomials,
            &mut witness_commitments,
        )?;

        assert_eq!(witness_polynomials.len(), witness_commitments.len());

        let accumulator_instances = accumulators.into_iter().map(|a| a.instance);
        let accumulator_witnesses = accumulators.into_iter().map(|a| a.witness);

        Self::compute_witness_polynomials_and_witnesses_from_inputs(
            ck,
            accumulator_instances,
            accumulator_witnesses,
            &mut witness_polynomials,
            &mut witness_commitments,
        )?;

        assert_eq!(witness_polynomials.len(), witness_commitments.len());

        Ok((witness_polynomials, witness_commitments))
    }

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

    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<lh_pc::Commitment<G>>>,
        challenges: &[G::ScalarField],
    ) -> lh_pc::Commitment<G> {
        let mut scalar_commitment_pairs = Vec::new();
        for (i, c) in commitments.into_iter().enumerate() {
            scalar_commitment_pairs.push((challenges[i], &c.commitment().0));
        }

        let combined_commitment = scalar_commitment_pairs.into_iter().sum();
        lh_pc::Commitment(combined_commitment)
    }

    fn basic_verify(
        input_instances: &Vec<&InputInstance<G>>,
        new_accumulator_instance: &InputInstance<G>,
        proof: &Proof<G>,
    ) -> bool {
        if input_instances.len() != proof.len() {
            return false;
        }

        for input_instance in input_instances {
            if input_instance.commitment.degree_bound().is_some() {
                return false;
            }
        }

        if new_accumulator_instance.commitment.degree_bound().is_some() {
            return false;
        }

        true
    }
}

impl<G, S> AccumulationScheme<ConstraintF<G>, S> for HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    type UniversalParams = ();
    type PredicateParams = lh_pc::UniversalParameters<G>;
    type PredicateIndex = usize;

    type ProverKey = lh_pc::CommitterKey<G>;
    type VerifierKey = usize;
    type DeciderKey = lh_pc::VerifierKey<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>;

    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>;

    type Proof = Proof<G>;

    type Error = BoxedError;

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ck, vk) = LinearHashPC::<G, DensePolynomial<G::ScalarField>>::trim(
            predicate_params,
            *predicate_index,
            0,
            None,
        )
        .map_err(|e| BoxedError::new(e))?;

        Ok((ck, *predicate_index, vk))
    }

    fn prove_with_sponge<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, S, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, S, Self>>,
        _make_zk: MakeZK<'_>,
        sponge: S,
    ) -> Result<(Accumulator<ConstraintF<G>, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        let inputs: Vec<InputRef<'a, _, _, Self>> = inputs.into_iter().collect();
        let accumulators: Vec<AccumulatorRef<'a, _, _, Self>> = old_accumulators.into_iter().collect();

        for (instance, witness, is_accumulator) in inputs
            .iter()
            .map(|input| (&input.instance, &input.witness, false))
            .chain(
                accumulators
                    .iter()
                    .map(|accumulator| (&accumulator.instance, &accumulator.witness, true)),
            )
        {
            if instance.commitment.degree_bound().is_some() || witness.degree_bound().is_some() {
                if is_accumulator {
                    return Err(BoxedError::new(ASError::MalformedAccumulator(
                        "Degree bounds on accumulators unsupported".to_string(),
                    )));
                }

                return Err(BoxedError::new(ASError::MalformedInput(
                    "Degree bounds on inputs unsupported".to_string(),
                )));
            }

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
        }

        let input_instances: Vec<&InputInstance<G>> = inputs
            .iter()
            .map(|input| input.instance)
            .chain(accumulators.iter().map(|accumulator| accumulator.instance))
            .collect();

        let input_witnesses: Vec<&Self::InputWitness> = inputs
            .iter()
            .map(|input| input.witness)
            .chain(accumulators.iter().map(|accumulator| accumulator.witness))
            .collect();

        let (witness_polynomials, witness_commitments) =
            Self::compute_witness_polynomials_and_commitments(
                &prover_key,
                inputs.as_slice(),
                accumulators.as_slice(),
            )
            .map_err(|e| BoxedError::new(e))?;

        assert_eq!(input_witnesses.len(), witness_polynomials.len());
        assert_eq!(input_witnesses.len(), witness_commitments.len());

        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(&prover_key.supported_degree());

        for (instance, witness_commitment) in input_instances.iter().zip(&witness_commitments) {
            absorb![
                &mut challenge_point_sponge,
                instance,
                witness_commitment.commitment().0 .0
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
            let input_witness_eval = input_witness.evaluate(&challenge_point);
            let witness_eval = witness_polynomial.evaluate(&challenge_point);

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

        let linear_combination_challenges = linear_combination_challenges_sponge
            .squeeze_nonnative_field_elements_with_sizes(
                vec![FieldElementSize::Truncated(128); proof.len() * 2].as_slice(),
            );

        let combined_polynomial = Self::combine_polynomials(
            input_witnesses.into_iter().chain(&witness_polynomials),
            linear_combination_challenges.as_slice(),
        );

        let combined_polynomial =
            LabeledPolynomial::new(PolynomialLabel::new(), combined_polynomial, None, None);

        let combined_eval = combined_polynomial.evaluate(&challenge_point);

        let combined_commitment = Self::combine_commitments(
            input_instances
                .into_iter()
                .map(|instance| &instance.commitment)
                .chain(&witness_commitments),
            linear_combination_challenges.as_slice(),
        );

        let combined_commitment =
            LabeledCommitment::new(PolynomialLabel::new(), combined_commitment, None);

        let new_accumulator_instance = InputInstance {
            commitment: combined_commitment,
            point: challenge_point,
            eval: combined_eval,
        };

        let new_accumulator = Accumulator::<_, _, Self> {
            instance: new_accumulator_instance,
            witness: combined_polynomial,
        };

        Ok((new_accumulator, proof))
    }

    fn verify_with_sponge<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: S,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        let mut input_instances = input_instances
            .into_iter()
            .chain(old_accumulator_instances)
            .collect::<Vec<_>>();

        if !Self::basic_verify(&input_instances, new_accumulator_instance, proof) {
            return Ok(false);
        }

        let mut challenge_point_sponge = sponge.clone();
        challenge_point_sponge.absorb(verifier_key);

        let mut commitments = Vec::new();
        for (input_instance, p) in input_instances.into_iter().zip(proof)
        {
            absorb![
                &mut challenge_point_sponge,
                input_instance,
                p.witness_commitment.commitment().0 .0
            ];

            let eval_check_lhs = p.eval - &input_instance.eval;
            let eval_check_rhs = p
                .witness_eval
                .mul(&(new_accumulator_instance.point - &input_instance.point));

            if !eval_check_lhs.eq(&eval_check_rhs) {
                return Ok(false);
            }

            commitments.push(&input_instance.commitment);
        }

        let challenge_point: G::ScalarField = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(184)])
            .pop()
            .unwrap();

        if !challenge_point.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

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

    fn decide_with_sponge(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, S, Self>,
        _sponge: S,
    ) -> Result<bool, Self::Error> {
        let check = LinearHashPC::check_individual_opening_challenges(
            decider_key,
            vec![&accumulator.instance.commitment],
            &accumulator.instance.point,
            vec![accumulator.instance.eval],
            &lh_pc::Proof(accumulator.witness.clone()),
            &|_| G::ScalarField::one(),
            None,
        );

        Ok(check.is_ok() && check.ok().unwrap())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ConstraintF;
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::hc_as::{HomomorphicCommitmentAS, InputInstance};
    use crate::tests::*;
    use crate::AccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ff::ToConstraintField;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::lh_pc::LinearHashPC;
    use ark_poly_commit::{
        lh_pc, LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial,
    };
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct HcASTestParams {
        pub(crate) degree: usize,
        pub(crate) make_zk: bool,
    }

    pub struct HcASTestInput {}

    impl<G, S> ASTestInput<ConstraintF<G>, S, HomomorphicCommitmentAS<G, S>> for HcASTestInput
    where
        G: AffineCurve + ToConstraintField<ConstraintF<G>> + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = HcASTestParams;
        type InputParams = (lh_pc::CommitterKey<G>, lh_pc::VerifierKey<G>, bool);

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <HomomorphicCommitmentAS<G, S> as AccumulationScheme<ConstraintF<G>, S>>::PredicateParams,
            <HomomorphicCommitmentAS<G, S> as AccumulationScheme<ConstraintF<G>, S>>::PredicateIndex,
        ){
            let max_degree = test_params.degree;
            let supported_degree = max_degree;
            let supported_hiding_bound = if test_params.make_zk {
                supported_degree
            } else {
                0
            };

            let predicate_params =
                LinearHashPC::<G, DensePolynomial<G::ScalarField>>::setup(max_degree, None, rng)
                    .unwrap();

            let (ck, vk) = LinearHashPC::<G, DensePolynomial<G::ScalarField>>::trim(
                &predicate_params,
                supported_degree,
                supported_hiding_bound,
                None,
            )
            .unwrap();

            (
                (ck, vk, test_params.make_zk),
                predicate_params,
                supported_degree,
            )
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<ConstraintF<G>, S, HomomorphicCommitmentAS<G, S>>> {
            let ck = &input_params.0;
            let degree = PCCommitterKey::supported_degree(ck);

            let make_zk = input_params.2;
            let hiding_bound = if make_zk { Some(degree) } else { None };

            let labeled_polynomials: Vec<
                LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
            > = (0..num_inputs)
                .map(|i| {
                    //let degree =
                    //rand::distributions::Uniform::from(2..=ck.supported_degree()).sample(rng);
                    let label = format!("Input{}", i);

                    let polynomial = DensePolynomial::rand(degree, rng);
                    let labeled_polynomial =
                        LabeledPolynomial::new(label, polynomial, None, hiding_bound);

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, _) =
                LinearHashPC::<G, DensePolynomial<G::ScalarField>>::commit(
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

                    Input::<_, _, HomomorphicCommitmentAS<G, S>> {
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

    type AS = HomomorphicCommitmentAS<G, Sponge>;
    type I = HcASTestInput;

    type Tests = ASTests<CF, Sponge, AS, I>;

    #[test]
    pub fn single_input_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&HcASTestParams {
            degree: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&HcASTestParams {
            degree: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&HcASTestParams {
            degree: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&HcASTestParams {
            degree: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&HcASTestParams {
            degree: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&HcASTestParams {
            degree: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&HcASTestParams {
            degree: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&HcASTestParams {
            degree: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&HcASTestParams {
            degree: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&HcASTestParams {
            degree: 8,
            make_zk: true,
        })
    }
}
