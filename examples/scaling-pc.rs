#![allow(non_camel_case_types)]
// For randomness (during paramgen and proof generation)
// PS: thread_rng is *insecure*

// For benchmarking
use crate::ipa_pc_as::IpaPCDomain;
use ark_accumulation::ipa_pc_as;
use ark_ff::PrimeField;
use ark_pallas::{Affine as G1Affine, Fq, Fr};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::ipa_pc::InnerProductArgPC;
use ark_poly_commit::trivial_pc::TrivialPC;
use ark_poly_commit::{LabeledPolynomial, PCCommitterKey, PolynomialCommitment, UVPolynomial};
use ark_serialize::CanonicalSerialize;
use ark_sponge::domain_separated::DomainSeparatedSponge;
use ark_sponge::poseidon::PoseidonSponge;
use ark_std::rand::Rng;
use ark_std::vec::Vec;
use blake2::Blake2s;
use std::time::Instant;

type TrivPC = TrivialPC<G1Affine, DensePolynomial<Fr>>;

type IpaPC = InnerProductArgPC<
    G1Affine,
    Blake2s,
    DensePolynomial<Fr>,
    Fq,
    DomainSeparatedSponge<Fq, PoseidonSponge<Fq>, IpaPCDomain>,
>;

fn profile_pc<F, PC, R>(min_degree: usize, max_degree: usize, rng: &mut R)
where
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: Rng,
{
    println!("Performing setup!");
    let pc_pp = PC::setup(1 << max_degree, Some(1), rng).unwrap();
    println!("Done with setup!");

    for degree in min_degree..=max_degree {
        let degree = (1 << degree) - 1;
        println!("Degree: {:?}", degree);
        let supported_degree = degree;

        let start = Instant::now();
        let (ck, vk) = PC::trim(&pc_pp, supported_degree, 0, None).unwrap();
        let index_time = start.elapsed();
        println!("Indexer: {:?}", index_time.as_millis());

        let polynomials = vec![{
            let degree = ck.supported_degree();
            let label = format!("Input {}", 1);

            let polynomial = UVPolynomial::rand(degree, rng);
            let labeled_polynomial = LabeledPolynomial::new(label, polynomial, None, None);

            labeled_polynomial
        }];

        let start = Instant::now();
        let (comms, rands) = PC::commit(&ck, &polynomials, Some(rng)).unwrap();
        let commit_time = start.elapsed();
        println!("Committer: {:?}", commit_time.as_millis());

        let point = F::rand(rng);
        let values = vec![polynomials[0].evaluate(&point)];
        let opening_challenge = F::one();

        let start = Instant::now();
        let proof = PC::open(
            &ck,
            &polynomials,
            &comms,
            &point,
            opening_challenge,
            &rands,
            Some(rng),
        )
        .unwrap();
        let open_time = start.elapsed();
        println!("Open: {:?}", open_time.as_millis());

        let start = Instant::now();
        assert!(PC::check(
            &vk,
            &comms,
            &point,
            values,
            &proof,
            opening_challenge,
            Some(rng)
        )
        .unwrap());
        let check_time = start.elapsed();
        println!("Check: {:?}\n", check_time.as_millis());

        println!("Proof size: {}", proof.serialized_size());
        println!("\n\n");
    }
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
    println!("\n\n\n================ Benchmarking PC_LH ================");
    profile_pc::<_, TrivPC, _>(min_degree, max_degree, rng);
    println!("\n\n\n================ Benchmarking IpaPC ================");
    profile_pc::<_, IpaPC, _>(min_degree, max_degree, rng);
}
