#![allow(non_camel_case_types)]
// For randomness (during paramgen and proof generation)
// PS: thread_rng is *insecure*

// For benchmarking
use ark_ff::{One, PrimeField};
use ark_pallas::{Affine as G1Affine, Fq, Fr};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use rand::Rng;
use std::time::Instant;

// struct ProfileData {
//     size: Vec<usize>,
//     index_setup_times: Vec<f64>,
//     prover_times: Vec<f64>,
//     verifier_times: Vec<f64>,
//     decider_times: Vec<f64>,
// }

use ark_accumulation::{hc_as, hc_as::HomomorphicCommitmentAS};
use ark_accumulation::{ipa_as, ipa_as::InnerProductArgAtomicAS};
use ark_accumulation::{AccumulationScheme, Accumulator, Input, MakeZK};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::lh_pc::LinearHashPC;
use ark_poly_commit::{LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial};
use ark_sponge::poseidon::PoseidonSponge;
use ark_std::vec::Vec;
use rand_core::RngCore;

type PCLH = LinearHashPC<G1Affine, DensePolynomial<Fr>>;
type AS_LH = HomomorphicCommitmentAS<G1Affine, PoseidonSponge<Fq>>;

type PCDL = ipa_as::IpaPC<G1Affine, PoseidonSponge<Fq>>;
type AS_DL = InnerProductArgAtomicAS<G1Affine, PoseidonSponge<Fq>>;

fn profile_as<F, P, PC, AS, R, ParamGen, InputGen>(
    min_degree: usize,
    max_degree: usize,
    sample_parameters_and_index: ParamGen,
    sample_inputs: InputGen,
    rng: &mut R,
) where
    F: PrimeField,
    P: UVPolynomial<F>,
    PC: PolynomialCommitment<F, P>,
    AS: AccumulationScheme,
    ParamGen: Fn(
        usize,
        &mut R,
    ) -> (
        (PC::CommitterKey, PC::VerifierKey),
        AS::PredicateParams,
        AS::PredicateIndex,
    ),
    InputGen: Fn(&PC::CommitterKey, &mut R) -> Vec<Input<AS>>,
    R: Rng,
{
    for degree in min_degree..=max_degree {
        let degree = (1 << degree) - 1;
        println!("Degree: {:?}", degree);
        let supported_degree = degree;

        let ((ck, _), predicate_params, predicate_index) =
            sample_parameters_and_index(supported_degree, rng);
        let as_pp = AS::generate(rng).unwrap();

        let start = Instant::now();
        let (pk, vk, dk) = AS::index(&as_pp, &predicate_params, &predicate_index).unwrap();
        let index_time = start.elapsed();
        println!("Indexer: {:?}", index_time.as_millis());

        let inputs = sample_inputs(&ck, rng);

        // Initially start with empty accumulators
        let mut old_accumulators = Vec::with_capacity(1);

        let (accumulator, _) = AS::prove(
            &pk,
            Input::<AS>::map_to_refs(&inputs),
            Accumulator::<AS>::map_to_refs(&old_accumulators),
            MakeZK::Inherited(Some(rng)),
        )
        .unwrap();

        // Use the same accumulator as input
        old_accumulators.push(accumulator.clone());
        old_accumulators.push(accumulator.clone());

        let start = Instant::now();
        let (accumulator, proof) = AS::prove(
            &pk,
            Input::<AS>::map_to_refs(&inputs),
            Accumulator::<AS>::map_to_refs(&old_accumulators),
            MakeZK::Inherited(Some(rng)),
        )
        .unwrap();
        let prover_time = start.elapsed();
        println!("Prover: {:?}", prover_time.as_millis());

        let start = Instant::now();
        let verification_result = AS::verify(
            &vk,
            Input::<AS>::instances(&inputs),
            Accumulator::<AS>::instances(&old_accumulators),
            &accumulator.instance,
            &proof,
        )
        .unwrap();
        let verifier_time = start.elapsed();
        println!("Verifier: {:?}", verifier_time.as_millis());

        let start = Instant::now();
        let decision_result = AS::decide(&dk, accumulator.as_ref()).unwrap();
        let decider_time = start.elapsed();
        println!("Decider: {:?}\n", decider_time.as_millis());
        println!("Accumulator size: {}", accumulator.serialized_size());
        println!(
            "Accumulator instance size: {}",
            accumulator.instance.serialized_size()
        );
        println!(
            "Accumulator witness size: {}",
            accumulator.witness.serialized_size()
        );

        println!("\n\n");

        assert!(verification_result);
        assert!(decision_result);
    }
}

type PCLH_Keys = (
    <PCLH as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    <PCLH as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::VerifierKey,
);

fn lh_param_gen<R: RngCore>(
    degree: usize,
    rng: &mut R,
) -> (
    PCLH_Keys,
    <AS_LH as AccumulationScheme>::PredicateParams,
    <AS_LH as AccumulationScheme>::PredicateIndex,
) {
    let predicate_params = PCLH::setup(degree, None, rng).unwrap();
    let (ck, vk) = PCLH::trim(&predicate_params, degree, 0, None).unwrap();
    ((ck, vk), predicate_params, degree)
}

fn lh_input_gen<R: RngCore>(
    ck: &<PCLH as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    rng: &mut R,
) -> Vec<Input<AS_LH>> {
    let labeled_polynomials = vec![{
        let degree = ck.supported_degree();
        let label = format!("Input{}", 1);

        let polynomial = DensePolynomial::rand(degree, rng);
        let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

        labeled_polynomial
    }];

    let (labeled_commitments, _) = PCLH::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

    let inputs = labeled_polynomials
        .into_iter()
        .zip(labeled_commitments)
        .map(|(labeled_polynomial, labeled_commitment)| {
            let point = Fr::rand(rng);
            let eval = labeled_polynomial.evaluate(&point);

            let instance = hc_as::InputInstance {
                commitment: labeled_commitment,
                point,
                eval,
            };

            Input::<AS_LH> {
                instance,
                witness: labeled_polynomial,
            }
        })
        .collect();

    inputs
}

type PCDL_Keys = (
    <PCDL as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    <PCDL as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::VerifierKey,
);

fn dl_param_gen<R: RngCore>(
    degree: usize,
    rng: &mut R,
) -> (
    PCDL_Keys,
    <AS_DL as AccumulationScheme>::PredicateParams,
    <AS_DL as AccumulationScheme>::PredicateIndex,
) {
    let predicate_params = PCDL::setup(degree, None, rng).unwrap();
    let (ck, vk) = PCDL::trim(&predicate_params, degree, 0, None).unwrap();
    let predicate_index = ipa_as::PredicateIndex {
        supported_degree_bound: degree,
        supported_hiding_bound: 0,
    };
    ((ck, vk), predicate_params, predicate_index)
}

fn dl_input_gen<R: RngCore>(
    ck: &<PCDL as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    rng: &mut R,
) -> Vec<Input<AS_DL>> {
    let labeled_polynomials = vec![{
        let degree = ck.supported_degree();
        let label = format!("Input{}", 1);

        let polynomial = DensePolynomial::rand(degree, rng);
        let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

        labeled_polynomial
    }];

    let (labeled_commitments, randoms) = PCDL::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

    let inputs = labeled_polynomials
        .into_iter()
        .zip(labeled_commitments)
        .zip(randoms)
        .map(|((labeled_polynomial, labeled_commitment), randomness)| {
            let point = Fr::rand(rng);
            let eval = labeled_polynomial.evaluate(&point);
            let ipa_proof = PCDL::open_individual_opening_challenges(
                ck,
                vec![&labeled_polynomial],
                vec![&labeled_commitment],
                &point,
                &|_| Fr::one(),
                &vec![randomness],
                Some(rng),
            )
            .unwrap();
            let result = PCDL::check_individual_opening_challenges(
                ck,
                vec![&labeled_commitment],
                &point,
                vec![eval],
                &ipa_proof,
                &|_| Fr::one(),
                Some(rng),
            )
            .unwrap();
            assert!(result);

            let input = ipa_as::InputInstance {
                ipa_commitment: labeled_commitment,
                point,
                evaluation: eval,
                ipa_proof,
            };

            Input::<AS_DL> {
                instance: input,
                witness: (),
            }
        })
        .collect();

    inputs
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 || args[1] == "-h" || args[1] == "--help" {
        println!("\nHelp: Invoke this as <program> <log_min_degree> <log_max_degree>\n");
    }
    let min_degree: usize = String::from(args[1].clone())
        .parse()
        .expect("<log_min_degree> should be integer");
    let max_degree: usize = String::from(args[2].clone())
        .parse()
        .expect("<log_max_degree> should be integer");

    let rng = &mut ark_std::test_rng();
    println!("\n\n\n================ Benchmarking AS_LH ================");
    profile_as::<_, _, PCLH, AS_LH, _, _, _>(
        min_degree,
        max_degree,
        lh_param_gen,
        lh_input_gen,
        rng,
    );
    println!("\n\n\n================ Benchmarking AS_DL ================");
    profile_as::<_, _, PCDL, AS_DL, _, _, _>(
        min_degree,
        max_degree,
        dl_param_gen,
        dl_input_gen,
        rng,
    );
}
