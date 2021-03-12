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

use ark_accumulation::ipa_as::IpaPCDomain;
use ark_accumulation::{hc_as, hc_as::HomomorphicCommitmentAS};
use ark_accumulation::{ipa_as, ipa_as::InnerProductArgAtomicAS};
use ark_accumulation::{AccumulationScheme, Accumulator, Input, MakeZK};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::ipa_pc::InnerProductArgPC;
use ark_poly_commit::pedersen_pc::PedersenPC;
use ark_poly_commit::{LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial};
use ark_sponge::domain_separated::DomainSeparatedSponge;
use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::CryptographicSponge;
use ark_std::vec::Vec;
use blake2::Blake2s;
use rand_core::RngCore;

type PedPC = PedersenPC<G1Affine, DensePolynomial<Fr>>;
type HcAS = HomomorphicCommitmentAS<G1Affine, PoseidonSponge<Fq>>;

type IpaPC = InnerProductArgPC<
    G1Affine,
    Blake2s,
    DensePolynomial<Fr>,
    Fq,
    DomainSeparatedSponge<Fq, PoseidonSponge<Fq>, IpaPCDomain>,
>;
type IpaAS = InnerProductArgAtomicAS<G1Affine, PoseidonSponge<Fq>>;

fn profile_as<F, P, PC, CF, S, AS, R, ParamGen, InputGen>(
    min_degree: usize,
    max_degree: usize,
    sample_parameters_and_index: ParamGen,
    sample_inputs: InputGen,
    rng: &mut R,
) where
    F: PrimeField,
    P: UVPolynomial<F>,
    PC: PolynomialCommitment<F, P>,
    CF: PrimeField,
    S: CryptographicSponge<CF>,
    AS: AccumulationScheme<CF, S>,
    ParamGen: Fn(
        usize,
        &mut R,
    ) -> (
        (PC::CommitterKey, PC::VerifierKey),
        AS::PredicateParams,
        AS::PredicateIndex,
    ),
    InputGen: Fn(&PC::CommitterKey, &mut R) -> Vec<Input<CF, S, AS>>,
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
            Input::<CF, S, AS>::map_to_refs(&inputs),
            Accumulator::<CF, S, AS>::map_to_refs(&old_accumulators),
            MakeZK::Inherited(Some(rng)),
        )
        .unwrap();

        // Use the same accumulator as input
        old_accumulators.push(accumulator.clone());
        old_accumulators.push(accumulator.clone());

        let start = Instant::now();
        let (accumulator, proof) = AS::prove(
            &pk,
            Input::<CF, S, AS>::map_to_refs(&inputs),
            Accumulator::<CF, S, AS>::map_to_refs(&old_accumulators),
            MakeZK::Inherited(Some(rng)),
        )
        .unwrap();
        let prover_time = start.elapsed();
        println!("Prover: {:?}", prover_time.as_millis());

        let start = Instant::now();
        let verification_result = AS::verify(
            &vk,
            Input::<CF, S, AS>::instances(&inputs),
            Accumulator::<CF, S, AS>::instances(&old_accumulators),
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

type PedPCKeys = (
    <PedPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    <PedPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::VerifierKey,
);

fn lh_param_gen<R: RngCore>(
    degree: usize,
    rng: &mut R,
) -> (
    PedPCKeys,
    <HcAS as AccumulationScheme<Fq, PoseidonSponge<Fq>>>::PredicateParams,
    <HcAS as AccumulationScheme<Fq, PoseidonSponge<Fq>>>::PredicateIndex,
) {
    let predicate_params = PedPC::setup(degree, None, rng).unwrap();
    let (ck, vk) = PedPC::trim(&predicate_params, degree, 0, None).unwrap();
    ((ck, vk), predicate_params, degree)
}

fn lh_input_gen<R: RngCore>(
    ck: &<PedPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    rng: &mut R,
) -> Vec<Input<Fq, PoseidonSponge<Fq>, HcAS>> {
    let labeled_polynomials = vec![{
        let degree = ck.supported_degree();
        let label = format!("Input{}", 1);

        let polynomial = DensePolynomial::rand(degree, rng);
        let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

        labeled_polynomial
    }];

    let (labeled_commitments, _) = PedPC::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

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

            Input::<_, _, HcAS> {
                instance,
                witness: labeled_polynomial,
            }
        })
        .collect();

    inputs
}

type IpaPC_Keys = (
    <IpaPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    <IpaPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::VerifierKey,
);

fn dl_param_gen<R: RngCore>(
    degree: usize,
    rng: &mut R,
) -> (
    IpaPC_Keys,
    <IpaAS as AccumulationScheme<Fq, PoseidonSponge<Fq>>>::PredicateParams,
    <IpaAS as AccumulationScheme<Fq, PoseidonSponge<Fq>>>::PredicateIndex,
) {
    let predicate_params = IpaPC::setup(degree, None, rng).unwrap();
    let (ck, vk) = IpaPC::trim(&predicate_params, degree, 0, None).unwrap();
    let predicate_index = ipa_as::PredicateIndex {
        supported_degree_bound: degree,
        supported_hiding_bound: 0,
    };
    ((ck, vk), predicate_params, predicate_index)
}

fn dl_input_gen<R: RngCore>(
    ck: &<IpaPC as PolynomialCommitment<Fr, DensePolynomial<Fr>>>::CommitterKey,
    rng: &mut R,
) -> Vec<Input<Fq, PoseidonSponge<Fq>, IpaAS>> {
    let labeled_polynomials = vec![{
        let degree = ck.supported_degree();
        let label = format!("Input{}", 1);

        let polynomial = DensePolynomial::rand(degree, rng);
        let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

        labeled_polynomial
    }];

    let (labeled_commitments, randoms) =
        IpaPC::commit(ck, &labeled_polynomials, Some(rng)).unwrap();

    let inputs = labeled_polynomials
        .into_iter()
        .zip(labeled_commitments)
        .zip(randoms)
        .map(|((labeled_polynomial, labeled_commitment), randomness)| {
            let point = Fr::rand(rng);
            let eval = labeled_polynomial.evaluate(&point);
            let ipa_proof = IpaPC::open_individual_opening_challenges(
                ck,
                vec![&labeled_polynomial],
                vec![&labeled_commitment],
                &point,
                &|_| Fr::one(),
                &vec![randomness],
                Some(rng),
            )
            .unwrap();
            let result = IpaPC::check_individual_opening_challenges(
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

            Input::<_, _, IpaAS> {
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
    println!("\n\n\n================ Benchmarking HcAS ================");
    profile_as::<_, _, PedPC, _, _, HcAS, _, _, _>(
        min_degree,
        max_degree,
        lh_param_gen,
        lh_input_gen,
        rng,
    );
    println!("\n\n\n================ Benchmarking IpaAS ================");
    profile_as::<_, _, IpaPC, _, _, IpaAS, _, _, _>(
        min_degree,
        max_degree,
        dl_param_gen,
        dl_input_gen,
        rng,
    );
}
