use crate::data_structures::{Accumulator, Input};
use crate::error::{ASError, BoxedError};
use crate::std::marker::PhantomData;
use crate::std::ops::{Add, Div};
use crate::std::string::ToString;
use crate::std::vec::Vec;
use crate::AidedAccumulationScheme;
use ark_ff::{to_bytes, PrimeField};
use ark_poly_commit::lh_pc::error::LHPCError;
use ark_poly_commit::lh_pc::linear_hash::LinearHashFunction;
use ark_poly_commit::lh_pc::LinearHashPC;
use ark_poly_commit::{
    lh_pc, LabeledCommitment, LabeledPolynomial, PCCommitterKey, PolynomialCommitment,
    PolynomialLabel, UVPolynomial,
};
use ark_sponge::{absorb, Absorbable, CryptographicSponge};
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

mod constraints;

pub struct LHAidedAccumulationScheme<F, P, LH, S>
where
    F: PrimeField + Absorbable<F>,
    P: UVPolynomial<F>,
    for<'a, 'b> &'a P: Add<&'b P, Output = P>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P>,
    LH: LinearHashFunction<F> + 'static,
    S: CryptographicSponge<F>,
{
    _field: PhantomData<F>,
    _polynomial: PhantomData<P>,
    _linear_hash_function: PhantomData<LH>,
    _sponge: PhantomData<S>,
}
impl<F, P, LH, S> LHAidedAccumulationScheme<F, P, LH, S>
where
    F: PrimeField + Absorbable<F>,
    P: UVPolynomial<F>,
    for<'a, 'b> &'a P: Add<&'b P, Output = P>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P>,
    LH: LinearHashFunction<F> + 'static,
    S: CryptographicSponge<F>,
{
    fn compute_witness_polynomials_and_witnesses_from_inputs<'a>(
        ck: &lh_pc::CommitterKey<F, LH>,
        input_instances: impl IntoIterator<Item = &'a InputInstance<F, LH>>,
        input_witnesses: impl IntoIterator<Item = &'a LabeledPolynomial<F, P>>,
        rng: &mut dyn RngCore,

        // Outputs
        witness_polynomials_output: &mut Vec<LabeledPolynomial<F, P>>,
        witness_commitments_output: &mut Vec<LabeledCommitment<lh_pc::Commitment<F, LH>>>,
    ) -> Result<(), LHPCError>
    where
        Self: 'a,
    {
        for (instance, witness) in input_instances.into_iter().zip(input_witnesses) {
            let point = instance.point;
            let eval = instance.eval;

            let numerator: P = (&P::from_coefficients_vec(vec![-eval])).add(witness.polynomial());
            let denominator = P::from_coefficients_vec(vec![-point, F::one()]);
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
        ck: &lh_pc::CommitterKey<F, LH>,
        inputs: &[&'a Input<Self>],
        accumulators: &[&'a Accumulator<Self>],
        rng: &mut dyn RngCore,
    ) -> Result<
        (
            Vec<LabeledPolynomial<F, P>>,
            Vec<LabeledCommitment<lh_pc::Commitment<F, LH>>>,
        ),
        LHPCError,
    >
    where
        Self: 'a,
    {
        let mut witness_polynomials = Vec::new();
        let mut witness_commitments = Vec::new();

        let input_instances = inputs.into_iter().map(|i| &i.instance);
        let input_witnesses = inputs.into_iter().map(|i| &i.witness);

        Self::compute_witness_polynomials_and_witnesses_from_inputs(
            ck,
            input_instances,
            input_witnesses,
            rng,
            &mut witness_polynomials,
            &mut witness_commitments,
        )?;

        assert_eq!(witness_polynomials.len(), witness_commitments.len());

        let accumulator_instances = accumulators.into_iter().map(|a| &a.instance);
        let accumulator_witnesses = accumulators.into_iter().map(|a| &a.witness);

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
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F, P>>,
        challenge: F,
    ) -> P
    where
        P: 'a,
    {
        let mut combined_polynomial = P::zero();
        let mut cur_challenge = F::one();
        for p in labeled_polynomials {
            combined_polynomial += (cur_challenge, p.polynomial());
            cur_challenge *= challenge;
        }

        combined_polynomial
    }

    fn combine_evaluations<'a>(evaluations: impl IntoIterator<Item = &'a F>, challenge: F) -> F {
        let mut combined_eval = F::zero();
        let mut cur_challenge = F::one();
        for eval in evaluations {
            combined_eval += &eval.mul(cur_challenge);
            cur_challenge *= challenge;
        }

        combined_eval
    }

    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<lh_pc::Commitment<F, LH>>>,
        challenge: F,
    ) -> lh_pc::Commitment<F, LH> {
        let mut scalar_commitment_pairs = Vec::new();
        let mut cur_challenge = F::one();
        for c in commitments {
            scalar_commitment_pairs.push((cur_challenge, &c.commitment().0));
            cur_challenge *= challenge;
        }

        let combined_commitment = scalar_commitment_pairs.into_iter().sum();
        lh_pc::Commitment(combined_commitment)
    }
}

impl<F, P, LH, S> AidedAccumulationScheme for LHAidedAccumulationScheme<F, P, LH, S>
where
    F: PrimeField + Absorbable<F>,
    P: UVPolynomial<F>,
    for<'a, 'b> &'a P: Add<&'b P, Output = P>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P>,
    LH: LinearHashFunction<F> + 'static,
    S: CryptographicSponge<F>,
{
    type PredicateParams = lh_pc::UniversalParameters<F, LH>;
    type PredicateIndex = usize;
    type UniversalParams = ();

    type ProverKey = ProverKey<F, LH>;
    type VerifierKey = F;
    type DeciderKey = lh_pc::VerifierKey<F, LH>;

    type InputInstance = InputInstance<F, LH>;
    type InputWitness = LabeledPolynomial<F, P>;

    type AccumulatorInstance = InputInstance<F, LH>;
    type AccumulatorWitness = LabeledPolynomial<F, P>;

    type Proof = Proof<F, LH>;

    type Error = BoxedError;

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ck, vk) = LinearHashPC::<F, P, LH>::trim(predicate_params, *predicate_index, 0, None)
            .map_err(|e| BoxedError::new(e))?;

        let mut degree_challenge_sponge = S::new();
        degree_challenge_sponge.absorb(predicate_index);

        let degree_challenge = degree_challenge_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        let prover_key = ProverKey {
            lh_ck: ck,
            degree_challenge,
        };

        Ok((prover_key, degree_challenge, vk))
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
        let rng = rng.expect("RngCore required for lh_as prove");

        let inputs: Vec<&Input<Self>> = inputs.into_iter().collect();
        let accumulators: Vec<&Accumulator<Self>> = accumulators.into_iter().collect();

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

        let input_instances: Vec<&InputInstance<F, LH>> = inputs
            .iter()
            .map(|input| &input.instance)
            .chain(accumulators.iter().map(|accumulator| &accumulator.instance))
            .collect();

        let input_witnesses: Vec<&Self::InputWitness> = inputs
            .iter()
            .map(|input| &input.witness)
            .chain(accumulators.iter().map(|accumulator| &accumulator.witness))
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
                &to_bytes!(witness_commitment.commitment()).unwrap()
            ];
        }

        let challenge_point = challenge_point_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        let mut linear_combination_challenge_sponge = S::new();
        linear_combination_challenge_sponge.absorb(&challenge_point);

        let mut proof = Vec::new();
        for ((input_witness, witness_polynomial), witness_commitment) in input_witnesses
            .iter()
            .zip(&witness_polynomials)
            .zip(&witness_commitments)
        {
            let input_witness_eval = input_witness.evaluate(&challenge_point);
            let witness_eval = witness_polynomial.evaluate(&challenge_point);

            absorb![
                &mut linear_combination_challenge_sponge,
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

        let linear_combination_challenge = linear_combination_challenge_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        let combined_polynomial = Self::combine_polynomials(
            input_witnesses.into_iter().chain(&witness_polynomials),
            linear_combination_challenge,
        );

        let combined_polynomial =
            LabeledPolynomial::new(PolynomialLabel::new(), combined_polynomial, None, None);

        let combined_eval = combined_polynomial.evaluate(&challenge_point);

        let combined_commitment = Self::combine_commitments(
            input_instances
                .into_iter()
                .map(|instance| &instance.commitment)
                .chain(&witness_commitments),
            linear_combination_challenge,
        );

        let combined_commitment =
            LabeledCommitment::new(PolynomialLabel::new(), combined_commitment, None);

        let new_accumulator_instance = InputInstance {
            commitment: combined_commitment,
            point: challenge_point,
            eval: combined_eval,
        };

        let new_accumulator = Accumulator {
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
                &to_bytes!(p.witness_commitment.commitment()).unwrap()
            ];

            let eval_check_lhs = p.eval - input_instance.eval;
            let eval_check_rhs = p
                .witness_eval
                .mul(new_accumulator_instance.point - &input_instance.point);

            if !eval_check_lhs.eq(&eval_check_rhs) {
                return Ok(false);
            }

            commitments.push(&input_instance.commitment);
        }

        let challenge_point = challenge_point_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        if !challenge_point.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

        let mut linear_combination_challenge_sponge = S::new();
        linear_combination_challenge_sponge.absorb(&challenge_point);

        for single_proof in proof {
            absorb![
                &mut linear_combination_challenge_sponge,
                &to_bytes!(&single_proof.eval).unwrap(),
                &to_bytes!(&single_proof.witness_eval).unwrap()
            ];
        }

        let linear_combination_challenge = linear_combination_challenge_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        let combined_eval = Self::combine_evaluations(
            proof
                .into_iter()
                .map(|p| &p.eval)
                .chain(proof.into_iter().map(|p| &p.witness_eval)),
            linear_combination_challenge,
        );

        if !combined_eval.eq(&new_accumulator_instance.eval) {
            return Ok(false);
        }

        let combined_commitment = Self::combine_commitments(
            commitments
                .into_iter()
                .chain(proof.into_iter().map(|p| &p.witness_commitment)),
            linear_combination_challenge,
        );

        if !combined_commitment.eq(new_accumulator_instance.commitment.commitment()) {
            return Ok(false);
        }

        Ok(true)
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: &Accumulator<Self>,
    ) -> Result<bool, Self::Error> {
        let check = LinearHashPC::check_individual_opening_challenges(
            decider_key,
            vec![&accumulator.instance.commitment],
            &accumulator.instance.point,
            vec![accumulator.instance.eval],
            &lh_pc::Proof(accumulator.witness.clone()),
            &|_| F::one(),
            None,
        );

        Ok(check.is_ok() && check.ok().unwrap())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::lh_as::{InputInstance, LHAidedAccumulationScheme};
    use crate::std::ops::Add;
    use crate::std::ops::Div;
    use crate::tests::*;
    use crate::AidedAccumulationScheme;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fr};
    use ark_ff::PrimeField;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly_commit::lh_pc::linear_hash::pedersen::PedersenCommitment;
    use ark_poly_commit::lh_pc::linear_hash::LinearHashFunction;
    use ark_poly_commit::lh_pc::LinearHashPC;
    use ark_poly_commit::{
        lh_pc, LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial,
    };
    use ark_sponge::digest_sponge::DigestSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use rand::distributions::Distribution;
    use rand_core::RngCore;

    pub struct LHAidedAccumulationSchemeTestInput {}

    impl<F, P, LH, S> AccumulationSchemeTestInput<LHAidedAccumulationScheme<F, P, LH, S>>
        for LHAidedAccumulationSchemeTestInput
    where
        F: PrimeField + Absorbable<F>,
        P: UVPolynomial<F>,
        for<'a, 'b> &'a P: Add<&'b P, Output = P>,
        for<'a, 'b> &'a P: Div<&'b P, Output = P>,
        LH: LinearHashFunction<F> + 'static,
        S: CryptographicSponge<F>,
    {
        type TestParams = ();
        type InputParams = (lh_pc::CommitterKey<F, LH>, lh_pc::VerifierKey<F, LH>);

        fn setup(
            _: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <LHAidedAccumulationScheme<F, P, LH, S> as AidedAccumulationScheme>::PredicateParams,
            <LHAidedAccumulationScheme<F, P, LH, S> as AidedAccumulationScheme>::PredicateIndex,
        ) {
            let max_degree = 50;
            let supported_degree = 50;
            let predicate_params = LinearHashPC::<F, P, LH>::setup(max_degree, None, rng).unwrap();

            let (ck, vk) =
                LinearHashPC::<F, P, LH>::trim(&predicate_params, supported_degree, 0, None)
                    .unwrap();

            ((ck, vk), predicate_params, supported_degree)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<LHAidedAccumulationScheme<F, P, LH, S>>> {
            let ck = &input_params.0;

            let labeled_polynomials: Vec<LabeledPolynomial<F, P>> = (0..num_inputs)
                .map(|i| {
                    let degree =
                        rand::distributions::Uniform::from(2..=ck.supported_degree()).sample(rng);
                    let label = format!("Input{}", i);

                    let polynomial = P::rand(degree, rng);
                    let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

                    labeled_polynomial
                })
                .collect();

            let (labeled_commitments, _) =
                LinearHashPC::<F, P, LH>::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

            let inputs = labeled_polynomials
                .into_iter()
                .zip(labeled_commitments)
                .map(|(labeled_polynomial, labeled_commitment)| {
                    let point = F::rand(rng);
                    let eval = labeled_polynomial.evaluate(&point);

                    let instance = InputInstance {
                        commitment: labeled_commitment,
                        point,
                        eval,
                    };

                    Input {
                        instance,
                        witness: labeled_polynomial,
                    }
                })
                .collect();

            inputs
        }
    }

    type AS = LHAidedAccumulationScheme<
        Fr,
        DensePolynomial<Fr>,
        PedersenCommitment<EdwardsAffine, sha2::Sha512>,
        DigestSponge<Fr, sha2::Sha512>,
    >;

    type I = LHAidedAccumulationSchemeTestInput;

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
