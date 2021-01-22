use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisMode, SynthesisError, ConstraintSynthesizer};
use ark_serialize::CanonicalSerialize;
use ark_snark::*;
use ark_sponge::*;
use ark_std::{UniformRand, marker::PhantomData};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{Field, ToConstraintField};
use blake2::{VarBlake2b, Blake2s, digest::{Digest, VariableOutput}};
use rand_core::SeedableRng;

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
    pub fn setup() -> PublicParameters {
        ()
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
        let ck = ark_std::cfg_into_iter!(0..num_constraints).map(|i| {
            let mut hasher = Blake2s::new();
            hasher.update(&matrices_hash);
            hasher.update(&i.to_le_bytes());
            let hash = hasher.finalize();
            let mut seed = [0u8; 32];
            seed.copy_from_slice(&hash);
            let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
            G::Projective::rand(&mut rng)
        }).collect::<Vec<_>>();
        let ck = G::Projective::batch_normalization_into_affine(ck.as_slice());
        Ok(Index {
            index_info,
            a,
            b,
            c,
            ck,
        })
    }

    pub fn prove() {

    }

    pub fn verify() {

    }
}