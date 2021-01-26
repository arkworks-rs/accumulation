use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisMode, SynthesisError, ConstraintSynthesizer};
use ark_serialize::CanonicalSerialize;
use ark_snark::*;
use ark_sponge::*;
use ark_std::{UniformRand, marker::PhantomData};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{Field, ToConstraintField, Zero, One};
use ark_poly_commit::pedersen::*;
use blake2::{VarBlake2b, Blake2s, digest::{Digest, VariableOutput}};
use rand_core::{RngCore, SeedableRng};

mod data_structures;
use data_structures::*;

type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
type R1CSResult<T> = Result<T, SynthesisError>;

/// A simple non-interactive argument of knowledge for R1CS. 
pub struct SimpleNARK<G, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> SimpleNARK<G, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    pub fn setup(max_num_constraints: usize) -> PublicParameters {
        PedersenCommitment::setup(max_num_constraints).unwrap().into()
    }

    pub fn index<C: ConstraintSynthesizer<G::ScalarField>>(pp: &PublicParameters, r1cs_instance: C) -> R1CSResult<Index<G>> {
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
        let (num_formatted_input_variables, num_witness_variables, num_constraints) = (
            ics.num_instance_variables(),
            ics.num_witness_variables(),
            ics.num_constraints(),
        );

        end_timer!(matrix_processing_time);

        let mut serialized_matrices = Vec::new();
        a.serialize(&mut serialized_matrices).unwrap();
        b.serialize(&mut serialized_matrices).unwrap();
        c.serialize(&mut serialized_matrices).unwrap();

        let mut hasher = VarBlake2b::new(32).unwrap();
        digest::Update::update(&mut hasher, &serialized_matrices);
        let mut matrices_hash = [0u8; 32]; 
        hasher.finalize_variable(|res| matrices_hash.copy_from_slice(res));

        let num_variables = num_formatted_input_variables + num_witness_variables;

        let index_info = IndexInfo {
            num_variables,
            num_constraints,
            num_instance_variables: num_formatted_input_variables,
            matrices_hash,
        };
        let ck = PedersenCommitment::trim(&pp, num_constraints).unwrap();
        Ok(Index { index_info, a, b, c, ck })
    }

    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>>(
        index: &Index<G>,
        r1cs: C,
        make_zk: bool,
        rng: Option<&mut dyn RngCore>
    ) -> R1CSResult<Proof<G>> {
        let init_time = start_timer!(|| "NARK::Prover::Init");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let pcs = ConstraintSystem::new_ref();
        pcs.set_optimization_goal(OptimizationGoal::Weight);
        pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
            construct_matrices: false,
        });
        r1cs.generate_constraints(pcs.clone())?;
        end_timer!(constraint_time);

        pcs.finalize();
        let (formatted_input_assignment, witness_assignment, num_constraints) = {
            let pcs = pcs.borrow().unwrap();
            (
                pcs.instance_assignment.as_slice().to_vec(),
                pcs.witness_assignment.as_slice().to_vec(),
                pcs.num_constraints,
            )
        };

        let num_input_variables = formatted_input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        let num_variables = num_input_variables + num_witness_variables;
        assert_eq!(index.index_info.num_variables, num_variables);
        assert_eq!(index.index_info.num_constraints, num_constraints);

        // Perform matrix multiplications
        let inner_prod_fn = |row: &[(G::ScalarField, usize)]| {
            let mut acc = G::ScalarField::zero();
            for &(ref coeff, i) in row {
                let tmp = if i < num_input_variables {
                    formatted_input_assignment[i]
                } else {
                    witness_assignment[i - num_input_variables]
                };

                acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
            }
            acc
        };

        let eval_z_a_time = start_timer!(|| "Evaluating z_A");
        let z_a = ark_std::cfg_iter!(index.a).map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_a_time);

        let eval_z_b_time = start_timer!(|| "Evaluating z_B");
        let z_b = ark_std::cfg_iter!(index.b).map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_b_time);

        let eval_z_c_time = start_timer!(|| "Evaluating z_C");
        let z_c = ark_std::cfg_iter!(index.c).map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_c_time);


        let (r, rng) = if make_zk {
            let rng = rng.unwrap();
            let r = Vec::with_capacity(num_witness_variables);
            for _ in 0..num_witness_variables {
                r.push(G::ScalarField::rand(&mut rng))
            }
            (Some(r), Some(rng))
        } else {
            (None, None)
        };

        end_timer!(init_time);
    }

    pub fn verify() {

    }
}