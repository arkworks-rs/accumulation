use crate::r1cs_nark_as::CHALLENGE_SIZE;
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_poly_commit::trivial_pc::PedersenCommitment;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
    SynthesisMode,
};
use ark_serialize::CanonicalSerialize;
use ark_sponge::{absorb, Absorb, CryptographicSponge, FieldElementSize};
use ark_std::rand::RngCore;
use ark_std::vec;
use ark_std::vec::Vec;
use ark_std::{cfg_into_iter, cfg_iter, marker::PhantomData, UniformRand};
use blake2::{digest::VariableOutput, VarBlake2b};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod data_structures;
pub use data_structures::*;

type R1CSResult<T> = Result<T, SynthesisError>;

pub(crate) const PROTOCOL_NAME: &[u8] = b"R1CS-NARK-2020";

/// A simple non-interactive argument of knowledge for R1CS.
/// The construction is described in detail in Section 8 of [\[BCLMS20\]][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618
pub struct R1CSNark<G, S>
where
    G: AffineCurve + Absorb,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> R1CSNark<G, S>
where
    G: AffineCurve + Absorb,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
{
    pub(crate) fn compute_challenge(
        matrices_hash: &[u8; 32],
        input: &[G::ScalarField],
        msg: &FirstRoundMessage<G>,
        mut sponge: S,
    ) -> G::ScalarField {
        sponge.absorb(&matrices_hash.as_ref());

        let input_bytes = input
            .iter()
            .flat_map(|inp| inp.into_repr().to_bytes_le())
            .collect::<Vec<_>>();

        absorb!(&mut sponge, input_bytes, msg);

        let out = sponge
            .squeeze_field_elements_with_sizes::<G::ScalarField>(&[FieldElementSize::Truncated(
                CHALLENGE_SIZE,
            )])
            .pop()
            .unwrap();

        out
    }

    /// Performs a setup for R1CS. This function does not currently do anything meaning.
    pub fn setup() -> PublicParameters {}

    /// Outputs a specialized prover and verifier key for some R1CS instance.
    pub fn index<C: ConstraintSynthesizer<G::ScalarField>>(
        _pp: &PublicParameters,
        r1cs_instance: C,
    ) -> R1CSResult<(IndexProverKey<G>, IndexVerifierKey<G>)> {
        let constraint_time = start_timer!(|| "Generating constraints");

        let ics = ConstraintSystem::new_ref();
        ics.set_optimization_goal(OptimizationGoal::Constraints);
        ics.set_mode(SynthesisMode::Setup);
        r1cs_instance.generate_constraints(ics.clone())?;

        end_timer!(constraint_time);

        let matrix_processing_time = start_timer!(|| "Processing matrices");
        ics.finalize();

        let matrices = ics.to_matrices().expect("should not be `None`");
        let (a, b, c) = (matrices.a, matrices.b, matrices.c);
        let (num_input_variables, num_witness_variables, num_constraints) = (
            ics.num_instance_variables(),
            ics.num_witness_variables(),
            ics.num_constraints(),
        );

        end_timer!(matrix_processing_time);

        let matrices_hash = hash_matrices(PROTOCOL_NAME, &a, &b, &c);

        let num_variables = num_input_variables + num_witness_variables;
        let pp = PedersenCommitment::setup(num_constraints);
        let ck = PedersenCommitment::trim(&pp, num_constraints);
        let index_info = IndexInfo {
            num_variables,
            num_constraints,
            num_instance_variables: num_input_variables,
            matrices_hash,
        };
        let ipk = IndexProverKey {
            index_info,
            a,
            b,
            c,
            ck,
        };
        let ivk = ipk.clone();
        Ok((ipk, ivk))
    }

    /// Proves that some R1CS relation holds.
    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>>(
        ipk: &IndexProverKey<G>,
        r1cs: C,
        make_zk: bool,
        sponge: Option<S>,
        mut rng: Option<&mut dyn RngCore>,
    ) -> R1CSResult<Proof<G>> {
        let init_time = start_timer!(|| "NARK::Prover");

        // Step 1 of the scheme's prover, as detailed in BCLMS20.
        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let pcs = ConstraintSystem::new_ref();
        pcs.set_optimization_goal(OptimizationGoal::Constraints);
        pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
            construct_matrices: false,
        });
        r1cs.generate_constraints(pcs.clone())?;
        end_timer!(constraint_time);

        pcs.finalize();
        let (input, witness, num_constraints) = {
            let pcs = pcs.borrow().unwrap();
            (
                pcs.instance_assignment.as_slice().to_vec(),
                pcs.witness_assignment.as_slice().to_vec(),
                pcs.num_constraints,
            )
        };

        let num_input_variables = input.len();
        let num_witness_variables = witness.len();
        let num_variables = num_input_variables + num_witness_variables;

        assert_eq!(ipk.index_info.num_variables, num_variables);
        assert_eq!(ipk.index_info.num_constraints, num_constraints);

        // Step 2 of the scheme's prover, as detailed in BCLMS20.
        let r = if make_zk {
            // Sample r
            let randomizer_time = start_timer!(|| "Sampling randomizer r");

            let rng = rng.as_mut().unwrap();
            let mut r = Vec::with_capacity(num_witness_variables);
            for _ in 0..num_witness_variables {
                r.push(G::ScalarField::rand(rng))
            }

            end_timer!(randomizer_time);

            Some(r)
        } else {
            None
        };

        // Step 3 of the scheme's prover, as detailed in BCLMS20.
        let eval_z_m_time = start_timer!(|| "Evaluating z_M");
        let z_a = matrix_vec_mul(&ipk.a, &input, &witness);
        let z_b = matrix_vec_mul(&ipk.b, &input, &witness);
        let z_c = matrix_vec_mul(&ipk.c, &input, &witness);
        end_timer!(eval_z_m_time);

        let (r_a, r_b, r_c) = if make_zk {
            let r_ref = r.as_ref().unwrap();
            let zeros = vec![G::ScalarField::zero(); num_input_variables];

            // Compute r_a, r_b, r_c.
            let eval_r_m_time = start_timer!(|| "Evaluating r_M");
            let r_a = matrix_vec_mul(&ipk.a, &zeros, r_ref);
            let r_b = matrix_vec_mul(&ipk.b, &zeros, r_ref);
            let r_c = matrix_vec_mul(&ipk.c, &zeros, r_ref);
            end_timer!(eval_r_m_time);

            (Some(r_a), Some(r_b), Some(r_c))
        } else {
            (None, None, None)
        };

        // Step 4 of the scheme's prover, as detailed in BCLMS20.
        // Sample blinders for z_a, z_b, z_c.
        let (mut a_blinder, mut b_blinder, mut c_blinder) = (None, None, None);
        if make_zk {
            let rng = rng.as_mut().unwrap();
            a_blinder = Some(G::ScalarField::rand(rng));
            b_blinder = Some(G::ScalarField::rand(rng));
            c_blinder = Some(G::ScalarField::rand(rng));
        }

        let commit_time = start_timer!(|| "Committing to z_A, z_B, and z_C");
        // Compute hiding commitments to z_a, z_b, z_c.
        let comm_a = PedersenCommitment::commit(&ipk.ck, &z_a, a_blinder);
        let comm_b = PedersenCommitment::commit(&ipk.ck, &z_b, b_blinder);
        let comm_c = PedersenCommitment::commit(&ipk.ck, &z_c, c_blinder);

        end_timer!(commit_time);

        let (mut r_a_blinder, mut r_b_blinder, mut r_c_blinder) = (None, None, None);
        let (mut blinder_1, mut blinder_2) = (None, None);
        let first_round_randomness = if make_zk {
            let rng = rng.as_mut().unwrap();

            // Sample blinders for r_a, r_b, r_c.
            r_a_blinder = Some(G::ScalarField::rand(rng));
            r_b_blinder = Some(G::ScalarField::rand(rng));
            r_c_blinder = Some(G::ScalarField::rand(rng));

            // Commit to r_a, r_b, r_c.
            let commit_time = start_timer!(|| "Committing to r_A, r_B, r_C");
            let comm_r_a = PedersenCommitment::commit(&ipk.ck, r_a.as_ref().unwrap(), r_a_blinder);
            let comm_r_b = PedersenCommitment::commit(&ipk.ck, r_b.as_ref().unwrap(), r_b_blinder);
            let comm_r_c = PedersenCommitment::commit(&ipk.ck, r_c.as_ref().unwrap(), r_c_blinder);
            end_timer!(commit_time);

            // Step 5 of the scheme's prover, as detailed in BCLMS20.
            // Commit to z_a ○ r_b + z_b ○ r_a.
            let cross_prod_time = start_timer!(|| "Computing cross product z_a ○ r_b + z_b ○ r_a");
            let z_a_times_r_b = cfg_iter!(z_a).zip(r_b.as_ref().unwrap());
            let z_b_times_r_a = cfg_iter!(z_b).zip(r_a.as_ref().unwrap());
            let cross_product: Vec<_> = z_a_times_r_b
                .zip(z_b_times_r_a)
                .map(|((z_a, r_b), (z_b, r_a))| *z_a * r_b + *z_b * r_a)
                .collect();
            end_timer!(cross_prod_time);
            blinder_1 = Some(G::ScalarField::rand(rng));
            let commit_time = start_timer!(|| "Committing to cross product");
            let comm_1 = PedersenCommitment::commit(&ipk.ck, &cross_product, blinder_1);
            end_timer!(commit_time);

            // Commit to r_a ○ r_b.
            let commit_time = start_timer!(|| "Committing to r_a ○ r_b");
            let r_a_r_b_product: Vec<_> = cfg_iter!(r_a.as_ref().unwrap())
                .zip(r_b.unwrap())
                .map(|(r_a, r_b)| r_b * r_a)
                .collect();
            blinder_2 = Some(G::ScalarField::rand(rng));
            let comm_2 = PedersenCommitment::commit(&ipk.ck, &r_a_r_b_product, blinder_2);
            end_timer!(commit_time);

            Some(FirstRoundMessageRandomness {
                comm_r_a,
                comm_r_b,
                comm_r_c,
                comm_1,
                comm_2,
            })
        } else {
            None
        };

        // Step 6 of the scheme's prover, as detailed in BCLMS20.
        let first_msg = FirstRoundMessage {
            comm_a,
            comm_b,
            comm_c,
            randomness: first_round_randomness,
        };

        // Step 7 of the scheme's prover, as detailed in BCLMS20.
        assert!(!sponge.is_none());
        let sponge = sponge.unwrap();
        let gamma =
            Self::compute_challenge(&ipk.index_info.matrices_hash, &input, &first_msg, sponge);

        let mut blinded_witness = witness;
        let second_round_randomness = if make_zk {
            // Step 8 of the scheme's prover, as detailed in BCLMS20.
            ark_std::cfg_iter_mut!(blinded_witness)
                .zip(r.unwrap())
                .for_each(|(s, r)| *s += gamma * r);

            // Step 9 of the scheme's prover, as detailed in BCLMS20.
            let sigma_a = a_blinder.unwrap() + gamma * r_a_blinder.unwrap();
            let sigma_b = b_blinder.unwrap() + gamma * r_b_blinder.unwrap();
            let sigma_c = c_blinder.unwrap() + gamma * r_c_blinder.unwrap();

            // Step 10 of the scheme's prover, as detailed in BCLMS20.
            let sigma_o = c_blinder.unwrap()
                + gamma * blinder_1.unwrap()
                + gamma.square() * blinder_2.unwrap();

            Some(SecondRoundMessageRandomness {
                sigma_a,
                sigma_b,
                sigma_c,
                sigma_o,
            })
        } else {
            None
        };

        // Step 11 of the scheme's prover, as detailed in BCLMS20.
        let second_msg = SecondRoundMessage {
            blinded_witness,
            randomness: second_round_randomness,
        };

        // Step 12 of the scheme's prover, as detailed in BCLMS20.
        let proof = Proof {
            first_msg,
            second_msg,
        };

        end_timer!(init_time);
        Ok(proof)
    }

    /// Verifies that some R1CS relation holds.
    pub fn verify(
        ivk: &IndexVerifierKey<G>,
        input: &[G::ScalarField],
        proof: &Proof<G>,
        sponge: Option<S>,
    ) -> bool {
        let init_time = start_timer!(|| "NARK::Verifier");
        if proof.first_msg.randomness.is_some() != proof.second_msg.randomness.is_some() {
            return false;
        }

        // Step 2 of the scheme's verifier, as detailed in BCLMS20.
        assert!(!sponge.is_none());
        let sponge = sponge.unwrap();
        let gamma = Self::compute_challenge(
            &ivk.index_info.matrices_hash,
            &input,
            &proof.first_msg,
            sponge,
        );

        // Step 3 of the scheme's verifier, as detailed in BCLMS20.
        let mat_vec_mul_time = start_timer!(|| "Computing M * blinded_witness");
        let a_times_blinded_witness =
            matrix_vec_mul(&ivk.a, &input, &proof.second_msg.blinded_witness);
        let b_times_blinded_witness =
            matrix_vec_mul(&ivk.b, &input, &proof.second_msg.blinded_witness);
        let c_times_blinded_witness =
            matrix_vec_mul(&ivk.c, &input, &proof.second_msg.blinded_witness);
        end_timer!(mat_vec_mul_time);

        // Step 4 of the scheme's verifier, as detailed in BCLMS20.
        let mut comm_a = proof.first_msg.comm_a.into_projective();
        let mut comm_b = proof.first_msg.comm_b.into_projective();
        let mut comm_c = proof.first_msg.comm_c.into_projective();
        if let Some(first_msg_randomness) = proof.first_msg.randomness.as_ref() {
            comm_a += first_msg_randomness.comm_r_a.mul(gamma);
            comm_b += first_msg_randomness.comm_r_b.mul(gamma);
            comm_c += first_msg_randomness.comm_r_c.mul(gamma);
        }

        let commit_time = start_timer!(|| "Reconstructing c_A, c_B, c_C commitments");
        let reconstructed_comm_a = PedersenCommitment::commit(
            &ivk.ck,
            &a_times_blinded_witness,
            proof.second_msg.randomness.as_ref().map(|r| r.sigma_a),
        );
        let reconstructed_comm_b = PedersenCommitment::commit(
            &ivk.ck,
            &b_times_blinded_witness,
            proof.second_msg.randomness.as_ref().map(|r| r.sigma_b),
        );
        let reconstructed_comm_c = PedersenCommitment::commit(
            &ivk.ck,
            &c_times_blinded_witness,
            proof.second_msg.randomness.as_ref().map(|r| r.sigma_c),
        );

        let a_equal = comm_a == reconstructed_comm_a.into_projective();
        let b_equal = comm_b == reconstructed_comm_b.into_projective();
        let c_equal = comm_c == reconstructed_comm_c.into_projective();
        drop(c_times_blinded_witness);
        end_timer!(commit_time);

        // Step 5 of the scheme's verifier, as detailed in BCLMS20.
        let had_prod_time = start_timer!(|| "Computing Hadamard product and commitment to it");
        let had_prod: Vec<_> = cfg_into_iter!(a_times_blinded_witness)
            .zip(b_times_blinded_witness)
            .map(|(a, b)| a * b)
            .collect();
        let reconstructed_had_prod_comm = PedersenCommitment::commit(
            &ivk.ck,
            &had_prod,
            proof.second_msg.randomness.as_ref().map(|r| r.sigma_o),
        );
        end_timer!(had_prod_time);

        let mut had_prod_comm = proof.first_msg.comm_c.into_projective();
        if let Some(first_msg_randomness) = proof.first_msg.randomness.as_ref() {
            had_prod_comm += first_msg_randomness.comm_1.mul(gamma);
            had_prod_comm += first_msg_randomness.comm_2.mul(gamma.square());
        }
        let had_prod_equal = had_prod_comm == reconstructed_had_prod_comm.into_projective();
        add_to_trace!(|| "Verifier result", || format!(
            "A equal: {}, B equal: {}, C equal: {}, Hadamard Product equal: {}",
            a_equal, b_equal, c_equal, had_prod_equal
        ));
        end_timer!(init_time);
        a_equal & b_equal & c_equal & had_prod_equal
    }
}

pub(crate) fn hash_matrices<F: Field>(
    domain_separator: &[u8],
    a: &Matrix<F>,
    b: &Matrix<F>,
    c: &Matrix<F>,
) -> [u8; 32] {
    let mut serialized_matrices = domain_separator.to_vec();
    a.serialize(&mut serialized_matrices).unwrap();
    b.serialize(&mut serialized_matrices).unwrap();
    c.serialize(&mut serialized_matrices).unwrap();

    let mut hasher = VarBlake2b::new(32).unwrap();
    digest::Update::update(&mut hasher, &serialized_matrices);

    let mut matrices_hash = [0u8; 32];
    hasher.finalize_variable(|res| matrices_hash.copy_from_slice(res));

    matrices_hash
}

// Computes `matrix * (input || witness)`.
pub(crate) fn matrix_vec_mul<F: Field>(matrix: &Matrix<F>, input: &[F], witness: &[F]) -> Vec<F> {
    ark_std::cfg_iter!(matrix)
        .map(|row| inner_prod(row, input, witness))
        .collect()
}

// Computes the inner product of `row` and `input || witness`
fn inner_prod<F: Field>(row: &[(F, usize)], input: &[F], witness: &[F]) -> F {
    let mut acc = F::zero();
    for &(ref coeff, i) in row {
        let tmp = if i < input.len() {
            input[i]
        } else {
            witness[i - input.len()]
        };

        acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
    }
    acc
}

#[cfg(test)]
pub(crate) mod test {
    use crate::tests::poseidon_parameters_for_test;

    use super::*;
    use ark_ff::{PrimeField, UniformRand};
    use ark_pallas::{Affine, Fq, Fr};
    use ark_relations::{
        lc,
        r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
    };
    use ark_sponge::poseidon::PoseidonSponge;
    const NUM_ITERS: usize = 10;

    #[derive(Copy, Clone)]
    struct DummyCircuit<F: PrimeField> {
        pub a: Option<F>,
        pub b: Option<F>,
        pub num_variables: usize,
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

            for _ in 0..(self.num_variables - 3) {
                cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..self.num_constraints - 1 {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
            }

            cs.enforce_constraint(lc!(), lc!(), lc!())?;

            Ok(())
        }
    }

    #[test]
    fn test_simple_circuit() {
        let rng = &mut ark_std::test_rng();
        let c = DummyCircuit {
            a: Some(Fr::rand(rng)),
            b: Some(Fr::rand(rng)),
            num_variables: 10,
            num_constraints: 100,
        };

        let pcs = ConstraintSystem::new_ref();
        pcs.set_optimization_goal(OptimizationGoal::Constraints);
        pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
            construct_matrices: false,
        });
        c.generate_constraints(pcs.clone()).unwrap();

        let r1cs_input = pcs.borrow().unwrap().instance_assignment.clone();

        let pp = R1CSNark::<Affine, PoseidonSponge<Fq>>::setup();
        let (ipk, ivk) = R1CSNark::<Affine, PoseidonSponge<Fq>>::index(&pp, c).unwrap();

        let start = ark_std::time::Instant::now();

        let sponge_param = poseidon_parameters_for_test::<Fq>();
        for i in 0..NUM_ITERS {
            let proof = R1CSNark::<Affine, PoseidonSponge<Fq>>::prove(
                &ipk,
                c.clone(),
                i % 2 == 1,
                Some(PoseidonSponge::<Fq>::new(&sponge_param)),
                Some(rng),
            )
            .unwrap();

            assert!(R1CSNark::<Affine, PoseidonSponge<Fq>>::verify(
                &ivk,
                &r1cs_input,
                &proof,
                Some(PoseidonSponge::<Fq>::new(&sponge_param)),
            ))
        }

        println!(
            "per-constraint proving time for {}: {} ns/constraint",
            stringify!($bench_pairing_engine),
            start.elapsed().as_nanos() / NUM_ITERS as u128 / 65536u128
        );
    }
}
