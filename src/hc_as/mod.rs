use crate::constraints::ConstraintF;
use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::std::marker::PhantomData;
use crate::std::ops::{Add, Div};
use crate::std::string::ToString;
use crate::std::vec::Vec;
use crate::AccumulationScheme;
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, One, PrimeField, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::lh_pc::LHPCError;
use ark_poly_commit::lh_pc::LinearHashPC;
use ark_poly_commit::{
    lh_pc, LabeledCommitment, LabeledPolynomial, PCCommitterKey, PolynomialCommitment,
    PolynomialLabel, UVPolynomial,
};
use ark_relations::r1cs::ToConstraintField;
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use data_structures::*;
use rand_core::RngCore;
use std::ops::Mul;

pub mod data_structures;

#[cfg(feature = "r1cs")]
pub mod constraints;

pub struct HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _curve: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    fn compute_witness_polynomials_and_witnesses_from_inputs<'a>(
        ck: &lh_pc::CommitterKey<G>,
        input_instances: impl IntoIterator<Item = &'a InputInstance<G>>,
        input_witnesses: impl IntoIterator<
            Item = &'a LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        >,
        rng: &mut dyn RngCore,

        // Outputs
        witness_polynomials_output: &mut Vec<
            LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
        >,
        witness_commitments_output: &mut Vec<LabeledCommitment<lh_pc::Commitment<G>>>,
    ) -> Result<(), LHPCError>
    where
        Self: 'a,
    {
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
                LinearHashPC::commit(ck, vec![&labeled_witness_polynomial], Some(rng))?.0;

            let witness_commitment = witness_commitments.pop().unwrap();

            witness_polynomials_output.push(labeled_witness_polynomial);
            witness_commitments_output.push(witness_commitment);
        }

        Ok(())
    }

    fn compute_witness_polynomials_and_commitments<'a>(
        ck: &lh_pc::CommitterKey<G>,
        inputs: &[InputRef<'a, Self>],
        accumulators: &[AccumulatorRef<'a, Self>],
        rng: &mut dyn RngCore,
    ) -> Result<
        (
            Vec<LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>>,
            Vec<LabeledCommitment<lh_pc::Commitment<G>>>,
        ),
        LHPCError,
    >
    where
        Self: 'a,
    {
        let mut witness_polynomials = Vec::new();
        let mut witness_commitments = Vec::new();

        let input_instances = inputs.into_iter().map(|i| i.instance);
        let input_witnesses = inputs.into_iter().map(|i| i.witness);

        Self::compute_witness_polynomials_and_witnesses_from_inputs(
            ck,
            input_instances,
            input_witnesses,
            rng,
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
            rng,
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
}

impl<G, S> AccumulationScheme for HomomorphicCommitmentAS<G, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    type UniversalParams = ();
    type PredicateParams = lh_pc::UniversalParameters<G>;
    type PredicateIndex = usize;

    type ProverKey = ProverKey<G, ConstraintF<G>>;
    type VerifierKey = ConstraintF<G>;
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

        let mut degree_challenge_sponge = S::new();
        degree_challenge_sponge.absorb(predicate_index);

        let degree_challenge = degree_challenge_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        let prover_key = ProverKey {
            lh_ck: ck,
            degree_challenge: degree_challenge.clone(),
        };

        Ok((prover_key, degree_challenge, vk))
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
        let rng = rng.ok_or_else(|| {
            BoxedError::new(ASError::MissingRng(
                "RngCore required for hc_as prove".to_string(),
            ))
        })?;

        let inputs: Vec<InputRef<'a, Self>> = inputs.into_iter().collect();
        let accumulators: Vec<AccumulatorRef<'a, Self>> = accumulators.into_iter().collect();

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

            if witness.degree() < 1 || witness.degree() > prover_key.lh_ck.supported_degree() {
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
                &prover_key.lh_ck,
                inputs.as_slice(),
                accumulators.as_slice(),
                rng,
            )
            .map_err(|e| BoxedError::new(e))?;

        assert_eq!(input_witnesses.len(), witness_polynomials.len());
        assert_eq!(input_witnesses.len(), witness_commitments.len());

        let mut challenge_point_sponge = S::new();
        challenge_point_sponge.absorb(&prover_key.degree_challenge);

        for (instance, witness_commitment) in input_instances.iter().zip(&witness_commitments) {
            absorb![
                &mut challenge_point_sponge,
                instance,
                witness_commitment
                    .commitment()
                    .0
                     .0
                    .to_field_elements()
                    .unwrap()
            ];
        }

        let challenge_point = challenge_point_sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])
            .pop()
            .unwrap();

        let mut linear_combination_challenges_sponge = S::new();
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
                vec![FieldElementSize::Truncated { num_bits: 128 }; proof.len() * 2].as_slice(),
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

        let new_accumulator = Accumulator::<Self> {
            instance: new_accumulator_instance,
            witness: combined_polynomial,
        };

        Ok((new_accumulator, proof))
    }

    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        if new_accumulator_instance.commitment.degree_bound().is_some() {
            return Ok(false);
        }

        let mut challenge_point_sponge = S::new();
        challenge_point_sponge.absorb(verifier_key);

        let mut commitments = Vec::new();
        for (input_instance, p) in input_instances
            .into_iter()
            .chain(accumulator_instances)
            .zip(proof)
        {
            if input_instance.commitment.degree_bound().is_some() {
                return Ok(false);
            }

            absorb![
                &mut challenge_point_sponge,
                input_instance,
                p.witness_commitment
                    .commitment()
                    .0
                     .0
                    .to_field_elements()
                    .unwrap()
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
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
                num_bits: 180,
            }])
            .pop()
            .unwrap();

        if !challenge_point.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

        let mut linear_combination_challenges_sponge = S::new();
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
                vec![FieldElementSize::Truncated { num_bits: 128 }; proof.len() * 2].as_slice(),
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

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<Self>,
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
    use crate::std::ops::Add;
    use crate::std::ops::Div;
    use crate::tests::*;
    use crate::AccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ff::{PrimeField, ToConstraintField};
    use ark_pallas::{Affine, Fq, Fr};
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::lh_pc::LinearHashPC;
    use ark_poly_commit::{
        lh_pc, LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial,
    };
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct HcPcASTestInput {}

    impl<G, S> ASTestInput<HomomorphicCommitmentAS<G, S>> for HcPcASTestInput
    where
        G: AffineCurve + ToConstraintField<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = ();
        type InputParams = (lh_pc::CommitterKey<G>, lh_pc::VerifierKey<G>);

        fn setup(
            _: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <HomomorphicCommitmentAS<G, S> as AccumulationScheme>::PredicateParams,
            <HomomorphicCommitmentAS<G, S> as AccumulationScheme>::PredicateIndex,
        ) {
            // TODO: Change these parameters to test params
            //let max_degree = (1 << 5) - 1;
            let max_degree = (1 << 2) - 1;
            let supported_degree = max_degree;
            let predicate_params =
                LinearHashPC::<G, DensePolynomial<G::ScalarField>>::setup(max_degree, None, rng)
                    .unwrap();

            let (ck, vk) = LinearHashPC::<G, DensePolynomial<G::ScalarField>>::trim(
                &predicate_params,
                supported_degree,
                0,
                None,
            )
            .unwrap();

            ((ck, vk), predicate_params, supported_degree)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<HomomorphicCommitmentAS<G, S>>> {
            let ck = &input_params.0;

            let labeled_polynomials: Vec<
                LabeledPolynomial<G::ScalarField, DensePolynomial<G::ScalarField>>,
            > = (0..num_inputs)
                .map(|i| {
                    //let degree =
                    //rand::distributions::Uniform::from(2..=ck.supported_degree()).sample(rng);
                    let degree = PCCommitterKey::supported_degree(ck);
                    let label = format!("Input{}", i);

                    let polynomial = DensePolynomial::rand(degree, rng);
                    let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

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

                    Input::<HomomorphicCommitmentAS<G, S>> {
                        instance,
                        witness: labeled_polynomial,
                    }
                })
                .collect();

            inputs
        }
    }

    type AS = HomomorphicCommitmentAS<Affine, PoseidonSponge<Fq>>;

    type I = HcPcASTestInput;

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
