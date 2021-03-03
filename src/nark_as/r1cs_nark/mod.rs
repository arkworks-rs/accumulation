use crate::constraints::ConstraintF;
use ark_ec::AffineCurve;
use ark_ff::{BigInteger, Field, One, PrimeField, ToConstraintField, Zero};
use ark_poly_commit::pedersen::*;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, Matrix, OptimizationGoal, SynthesisError,
    SynthesisMode,
};
use ark_serialize::CanonicalSerialize;
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::{cfg_into_iter, cfg_iter, marker::PhantomData, UniformRand};
use blake2::{digest::VariableOutput, VarBlake2b};
use data_structures::*;
use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod data_structures;
pub use data_structures::*;

type R1CSResult<T> = Result<T, SynthesisError>;

pub(crate) const PROTOCOL_NAME: &[u8] = b"Simple-R1CS-NARK-2020";

/// A simple non-interactive argument of knowledge for R1CS.
pub struct SimpleNARK<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> SimpleNARK<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    pub(crate) fn compute_challenge(
        index_info: &IndexInfo,
        input: &[G::ScalarField],
        msg: &FirstRoundMessage<G>,
    ) -> G::ScalarField {
        let mut sponge = S::new();
        sponge.absorb(&index_info.matrices_hash.as_ref());

        let input_bytes = input
            .iter()
            .flat_map(|inp| inp.into_repr().to_bytes_le())
            .collect::<Vec<_>>();

        absorb!(&mut sponge, input_bytes, msg);

        let out = sponge
            .squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated(128)])
            .pop()
            .unwrap();

        println!("{}", out);

        out
    }

    pub fn setup() -> PublicParameters {}

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
        let pp = PedersenCommitment::setup(num_constraints).unwrap();
        let ck = PedersenCommitment::trim(&pp, num_constraints).unwrap();
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

    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>>(
        ipk: &IndexProverKey<G>,
        r1cs: C,
        make_zk: bool,
        mut rng: Option<&mut dyn RngCore>,
    ) -> R1CSResult<Proof<G>> {
        let init_time = start_timer!(|| "NARK::Prover");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let pcs = ConstraintSystem::new_ref();
        pcs.set_optimization_goal(OptimizationGoal::Weight);
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

        let eval_z_m_time = start_timer!(|| "Evaluating z_M");
        let z_a = matrix_vec_mul(&ipk.a, &input, &witness);
        let z_b = matrix_vec_mul(&ipk.b, &input, &witness);
        let z_c = matrix_vec_mul(&ipk.c, &input, &witness);
        end_timer!(eval_z_m_time);

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
        let comm_a = PedersenCommitment::commit(&ipk.ck, &z_a, a_blinder)
            .unwrap()
            .0;
        let comm_b = PedersenCommitment::commit(&ipk.ck, &z_b, b_blinder)
            .unwrap()
            .0;
        let comm_c = PedersenCommitment::commit(&ipk.ck, &z_c, c_blinder)
            .unwrap()
            .0;
        end_timer!(commit_time);

        let mut r = None;
        let (mut comm_r_a, mut comm_r_b, mut comm_r_c) = (None, None, None);
        let (mut comm_1, mut comm_2) = (None, None);
        let (mut r_a_blinder, mut r_b_blinder, mut r_c_blinder) = (None, None, None);
        let (mut blinder_1, mut blinder_2) = (None, None);
        if make_zk {
            // Sample r.
            let randomizer_time = start_timer!(|| "Sampling randomizer r");
            let rng = rng.as_mut().unwrap();
            r = Some(Vec::with_capacity(num_witness_variables));
            r.as_mut().map(|v| {
                for _ in 0..num_witness_variables {
                    v.push(G::ScalarField::rand(rng))
                }
            });
            end_timer!(randomizer_time);
            let r_ref = r.as_ref().unwrap();
            let zeros = vec![G::ScalarField::zero(); num_input_variables];

            // Compute r_a, r_b, r_c.
            let eval_r_m_time = start_timer!(|| "Evaluating r_M");
            let r_a = matrix_vec_mul(&ipk.a, &zeros, r_ref);
            let r_b = matrix_vec_mul(&ipk.b, &zeros, r_ref);
            let r_c = matrix_vec_mul(&ipk.c, &zeros, r_ref);
            end_timer!(eval_r_m_time);

            // Sample blinders for r_a, r_b, r_c.
            r_a_blinder = Some(G::ScalarField::rand(rng));
            r_b_blinder = Some(G::ScalarField::rand(rng));
            r_c_blinder = Some(G::ScalarField::rand(rng));

            // Commit to r_a, r_b, r_c.
            let commit_time = start_timer!(|| "Committing to r_A, r_B, r_C");
            comm_r_a = Some(
                PedersenCommitment::commit(&ipk.ck, &r_a, r_a_blinder)
                    .unwrap()
                    .0,
            );
            comm_r_b = Some(
                PedersenCommitment::commit(&ipk.ck, &r_b, r_b_blinder)
                    .unwrap()
                    .0,
            );
            comm_r_c = Some(
                PedersenCommitment::commit(&ipk.ck, &r_c, r_c_blinder)
                    .unwrap()
                    .0,
            );
            end_timer!(commit_time);

            // Commit to z_a ○ r_b + z_b ○ r_a.
            let cross_prod_time = start_timer!(|| "Computing cross product z_a ○ r_b + z_b ○ r_a");
            let z_a_times_r_b = cfg_iter!(z_a).zip(&r_b);
            let z_b_times_r_a = cfg_iter!(z_b).zip(&r_a);
            let cross_product: Vec<_> = z_a_times_r_b
                .zip(z_b_times_r_a)
                .map(|((z_a, r_b), (z_b, r_a))| *z_a * r_b + *z_b * r_a)
                .collect();
            end_timer!(cross_prod_time);
            blinder_1 = Some(G::ScalarField::rand(rng));
            let commit_time = start_timer!(|| "Committing to cross product");
            comm_1 = Some(
                PedersenCommitment::commit(&ipk.ck, &cross_product, blinder_1)
                    .unwrap()
                    .0,
            );
            end_timer!(commit_time);

            // Commit to r_a ○ r_b.
            let commit_time = start_timer!(|| "Committing to r_a ○ r_b");
            let r_a_r_b_product: Vec<_> = cfg_iter!(r_a)
                .zip(r_b)
                .map(|(r_a, r_b)| r_b * r_a)
                .collect();
            blinder_2 = Some(G::ScalarField::rand(rng));
            comm_2 = Some(
                PedersenCommitment::commit(&ipk.ck, &r_a_r_b_product, blinder_2)
                    .unwrap()
                    .0,
            );
            end_timer!(commit_time);
        }
        let first_msg = FirstRoundMessage {
            comm_a,
            comm_b,
            comm_c,
            comm_r_a,
            comm_r_b,
            comm_r_c,
            comm_1,
            comm_2,
        };

        let gamma = Self::compute_challenge(&ipk.index_info, &input, &first_msg);

        let mut blinded_witness = witness;
        let (mut sigma_a, mut sigma_b, mut sigma_c) = (None, None, None);
        let mut sigma_o = None;
        if make_zk {
            ark_std::cfg_iter_mut!(blinded_witness)
                .zip(r.unwrap())
                .for_each(|(s, r)| *s += gamma * r);
            sigma_a = a_blinder.map(|a_blinder| a_blinder + gamma * r_a_blinder.unwrap());
            sigma_b = b_blinder.map(|b_blinder| b_blinder + gamma * r_b_blinder.unwrap());
            sigma_c = c_blinder.map(|c_blinder| c_blinder + gamma * r_c_blinder.unwrap());
            sigma_o = c_blinder.map(|c_blinder| {
                c_blinder + gamma * blinder_1.unwrap() + gamma.square() * blinder_2.unwrap()
            });
        }

        let second_msg = SecondRoundMessage {
            blinded_witness,
            sigma_a,
            sigma_b,
            sigma_c,
            sigma_o,
        };

        let proof = Proof {
            first_msg,
            second_msg,
            make_zk,
        };
        end_timer!(init_time);
        Ok(proof)
    }

    pub fn verify(ivk: &IndexVerifierKey<G>, input: &[G::ScalarField], proof: &Proof<G>) -> bool {
        let init_time = start_timer!(|| "NARK::Verifier");
        let make_zk = proof.make_zk;

        // format the input appropriately.
        let input = {
            let mut tmp = vec![G::ScalarField::one()];
            tmp.extend_from_slice(&input);
            tmp
        };

        let gamma = Self::compute_challenge(&ivk.index_info, &input, &proof.first_msg);

        let mat_vec_mul_time = start_timer!(|| "Computing M * blinded_witness");
        let a_times_blinded_witness =
            matrix_vec_mul(&ivk.a, &input, &proof.second_msg.blinded_witness);
        let b_times_blinded_witness =
            matrix_vec_mul(&ivk.b, &input, &proof.second_msg.blinded_witness);
        let c_times_blinded_witness =
            matrix_vec_mul(&ivk.c, &input, &proof.second_msg.blinded_witness);
        end_timer!(mat_vec_mul_time);
        let mut comm_a = proof.first_msg.comm_a.into_projective();
        let mut comm_b = proof.first_msg.comm_b.into_projective();
        let mut comm_c = proof.first_msg.comm_c.into_projective();
        if make_zk {
            comm_a += proof.first_msg.comm_r_a.unwrap().mul(gamma);
            comm_b += proof.first_msg.comm_r_b.unwrap().mul(gamma);
            comm_c += proof.first_msg.comm_r_c.unwrap().mul(gamma);
        }

        let commit_time = start_timer!(|| "Reconstructing c_A, c_B, c_C commitments");
        let reconstructed_comm_a =
            PedersenCommitment::commit(&ivk.ck, &a_times_blinded_witness, proof.second_msg.sigma_a)
                .unwrap()
                .0;
        let reconstructed_comm_b =
            PedersenCommitment::commit(&ivk.ck, &b_times_blinded_witness, proof.second_msg.sigma_b)
                .unwrap()
                .0;
        let reconstructed_comm_c =
            PedersenCommitment::commit(&ivk.ck, &c_times_blinded_witness, proof.second_msg.sigma_c)
                .unwrap()
                .0;

        let a_equal = comm_a == reconstructed_comm_a.into_projective();
        let b_equal = comm_b == reconstructed_comm_b.into_projective();
        let c_equal = comm_c == reconstructed_comm_c.into_projective();
        drop(c_times_blinded_witness);
        end_timer!(commit_time);

        let had_prod_time = start_timer!(|| "Computing Hadamard product and commitment to it");
        let had_prod: Vec<_> = cfg_into_iter!(a_times_blinded_witness)
            .zip(b_times_blinded_witness)
            .map(|(a, b)| a * b)
            .collect();
        let reconstructed_had_prod_comm =
            PedersenCommitment::commit(&ivk.ck, &had_prod, proof.second_msg.sigma_o)
                .unwrap()
                .0;
        end_timer!(had_prod_time);

        let mut had_prod_comm = proof.first_msg.comm_c.into_projective();
        if make_zk {
            had_prod_comm += proof.first_msg.comm_1.unwrap().mul(gamma);
            had_prod_comm += proof.first_msg.comm_2.unwrap().mul(gamma.square());
        }
        let had_prod_equal = had_prod_comm == reconstructed_had_prod_comm.into_projective();
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
    use super::*;
    use ark_ff::UniformRand;
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
        let v = c.a.unwrap() * &c.b.unwrap();

        let pp = SimpleNARK::<Affine, PoseidonSponge<Fq>>::setup();
        let (ipk, ivk) = SimpleNARK::<Affine, PoseidonSponge<Fq>>::index(&pp, c).unwrap();

        let start = ark_std::time::Instant::now();

        for i in 0..NUM_ITERS {
            let proof = SimpleNARK::<Affine, PoseidonSponge<Fq>>::prove(
                &ipk,
                c.clone(),
                i % 2 == 1,
                Some(rng),
            )
            .unwrap();
            assert!(SimpleNARK::<Affine, PoseidonSponge<Fq>>::verify(
                &ivk,
                &[v],
                &proof
            ))
        }

        println!(
            "per-constraint proving time for {}: {} ns/constraint",
            stringify!($bench_pairing_engine),
            start.elapsed().as_nanos() / NUM_ITERS as u128 / 65536u128
        );
    }
}