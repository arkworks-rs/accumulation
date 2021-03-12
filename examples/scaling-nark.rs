#![allow(non_camel_case_types)]
// For randomness (during paramgen and proof generation)
// PS: thread_rng is *insecure*

// For benchmarking
use ark_ff::PrimeField;
use rand::Rng;
use std::time::Instant;

use ark_accumulation::r1cs_nark::SimpleNARK;
use ark_serialize::CanonicalSerialize;
use ark_std::vec::Vec;

use ark_std::UniformRand;
use ark_pallas::{Affine, Fq, Fr};
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_sponge::poseidon::PoseidonSponge;

#[derive(Copy, Clone)]
struct DummyCircuit<F: PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_input_variables: usize,
    pub num_witness_variables: usize,
    pub num_constraints: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;

        for _ in 0..(self.num_input_variables - 1) {
            let _ =
                cs.new_input_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }
        for _ in 0..(self.num_witness_variables - 1) {
            let _ =
                cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..self.num_constraints - 1 {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        cs.enforce_constraint(lc!(), lc!(), lc!())?;

        Ok(())
    }
}

fn profile_nark<R: Rng>(min_constraints: usize, max_constraints: usize, make_zk: bool, rng: &mut R) {
    let pp = SimpleNARK::<Affine, PoseidonSponge<Fq>>::setup();
    let mut times = Vec::new();

    for num_constraints in min_constraints..=max_constraints {
        let num_constraints = 1 << num_constraints;
        let c = DummyCircuit {
            a: Some(Fr::rand(rng)),
            b: Some(Fr::rand(rng)),
            num_input_variables: 5,
            num_witness_variables: num_constraints - 5,
            num_constraints,
        };
        let a = c.a.unwrap();
        let v = a * &c.b.unwrap();

        let start = Instant::now();
        let (ipk, ivk) = SimpleNARK::<Affine, PoseidonSponge<Fq>>::index(&pp, c).unwrap();
        let index_time = start.elapsed().as_millis();

        let start = Instant::now();
        let proof = SimpleNARK::<Affine, PoseidonSponge<Fq>>::prove(
            &ipk,
            c.clone(),
            make_zk,
            Some(rng),
        ).unwrap();
        let prover_time = start.elapsed().as_millis();

        let start = Instant::now();
        assert!(SimpleNARK::<Affine, PoseidonSponge<Fq>>::verify(
            &ivk,
            &[v, a, a, a, a],
            &proof
        ));
        let verifier_time = start.elapsed().as_millis();
        let record = (num_constraints, index_time, prover_time, verifier_time);
        println!("(num_constraints, index_time, prover_time, verifier_time):\n{:?}", record);
        println!("Proof size: {}", proof.serialized_size());
        times.push(record)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 || args[1] == "-h" || args[1] == "--help" {
        println!("\nHelp: Invoke this as <program> <log_min_degree> <log_max_degree>\n");
    }
    let min_num_constraints: usize = String::from(args[1].clone())
        .parse()
        .expect("<log_num_constraints> should be integer");
    let max_num_constraints: usize = String::from(args[2].clone())
        .parse()
        .expect("<log_num_constraints> should be integer");

    let rng = &mut ark_std::test_rng();

    println!("\n\n\n================ Benchmarking NARK without zk ================");
    profile_nark(min_num_constraints, max_num_constraints, false, rng);

    println!("\n\n\n================ Benchmarking NARK with zk ================");
    profile_nark(min_num_constraints, max_num_constraints, true, rng);
}