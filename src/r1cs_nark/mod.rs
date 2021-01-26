use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisMode, SynthesisError, ConstraintSynthesizer};
use ark_serialize::CanonicalSerialize;
use ark_sponge::*;
use ark_std::{UniformRand, marker::PhantomData, cfg_iter};
use ark_ec::AffineCurve;
use ark_ff::{BigInteger, PrimeField, Field, ToConstraintField, Zero, One};
use ark_poly_commit::pedersen::*;
use blake2::{VarBlake2b, digest::VariableOutput};
use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
{
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

        let mut serialized_matrices = Vec::new();
        a.serialize(&mut serialized_matrices).unwrap();
        b.serialize(&mut serialized_matrices).unwrap();
        c.serialize(&mut serialized_matrices).unwrap();

        let mut hasher = VarBlake2b::new(32).unwrap();
        digest::Update::update(&mut hasher, &serialized_matrices);
        let mut matrices_hash = [0u8; 32]; 
        hasher.finalize_variable(|res| matrices_hash.copy_from_slice(res));

        let num_variables = num_input_variables + num_witness_variables;
        let pp = PedersenCommitment::setup(num_constraints).unwrap();
        let ck = PedersenCommitment::trim(&pp, num_constraints).unwrap();
        let index_info = IndexInfo {
            num_variables,
            num_constraints,
            num_instance_variables: num_input_variables,
            matrices_hash,
        };
        let ipk = IndexProverKey { index_info, a, b, c, ck };
        let ivk = ipk.clone();
        Ok((ipk, ivk))
    }

    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>>(
        ipk: &IndexProverKey<G>,
        r1cs: C,
        make_zk: bool,
        mut rng: Option<&mut dyn RngCore>
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

        // Perform matrix multiplications
        let inner_prod_fn = |row: &[(G::ScalarField, usize)], input: &[G::ScalarField], witness: &[G::ScalarField]| {
            let mut acc = G::ScalarField::zero();
            for &(ref coeff, i) in row {
                let tmp = if i < input.len() {
                    input[i]
                } else {
                    witness[i - input.len()]
                };

                acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
            }
            acc
        };

        let eval_z_m_time = start_timer!(|| "Evaluating z_M");
        let z_a = ark_std::cfg_iter!(ipk.a).map(|row| inner_prod_fn(row, &input, &witness)).collect::<Vec<_>>();
        let z_b = ark_std::cfg_iter!(ipk.b).map(|row| inner_prod_fn(row, &input, &witness)).collect::<Vec<_>>();
        let z_c = ark_std::cfg_iter!(ipk.c).map(|row| inner_prod_fn(row, &input, &witness)).collect::<Vec<_>>();
        end_timer!(eval_z_m_time);

        // Sample blinders for z_a, z_b, z_c.
        let (mut a_blinder, mut b_blinder, mut c_blinder) = (None, None, None);
        if make_zk {
            let rng = rng.as_mut().unwrap();
            a_blinder = Some(G::ScalarField::rand(rng));
            b_blinder = Some(G::ScalarField::rand(rng));
            c_blinder = Some(G::ScalarField::rand(rng));
        }

        // Compute hiding commitments to z_a, z_b, z_c.
        let comm_a = PedersenCommitment::commit(&ipk.ck, &z_a, a_blinder).unwrap();
        let comm_b = PedersenCommitment::commit(&ipk.ck, &z_b, b_blinder).unwrap();
        let comm_c = PedersenCommitment::commit(&ipk.ck, &z_c, c_blinder).unwrap();


        let mut r = None;
        let (mut comm_r_a, mut comm_r_b, mut comm_r_c) = (None, None, None);
        let (mut comm_1, mut comm_2) = (None, None);
        let (mut r_a_blinder, mut r_b_blinder, mut r_c_blinder) = (None, None, None);
        let (mut blinder_1, mut blinder_2) = (None, None);
        if make_zk {
            // Sample r.
            let rng = rng.as_mut().unwrap();
            r = Some(Vec::with_capacity(num_witness_variables));
            for _ in 0..num_witness_variables {
                r.as_mut().map(|v| v.push(G::ScalarField::rand(rng)));
            }
            let r_ref = r.as_ref().unwrap();
            let zeros = vec![G::ScalarField::zero(); num_input_variables];

            // Compute r_a, r_b, r_c.
            let eval_r_m_time = start_timer!(|| "Evaluating r_M");
            let r_a = ark_std::cfg_iter!(ipk.a).map(|row| inner_prod_fn(row, &zeros, r_ref)).collect::<Vec<_>>();
            let r_b = ark_std::cfg_iter!(ipk.b).map(|row| inner_prod_fn(row, &zeros, r_ref)).collect::<Vec<_>>();
            let r_c = ark_std::cfg_iter!(ipk.c).map(|row| inner_prod_fn(row, &zeros, r_ref)).collect::<Vec<_>>();
            end_timer!(eval_r_m_time);

            // Sample blinders for r_a, r_b, r_c.
            r_a_blinder = Some(G::ScalarField::rand(rng));
            r_b_blinder = Some(G::ScalarField::rand(rng));
            r_c_blinder = Some(G::ScalarField::rand(rng));

            // Commit to r_a, r_b, r_c.
            comm_r_a = Some(PedersenCommitment::commit(&ipk.ck, &r_a, r_a_blinder).unwrap());
            comm_r_b = Some(PedersenCommitment::commit(&ipk.ck, &r_b, r_b_blinder).unwrap());
            comm_r_c = Some(PedersenCommitment::commit(&ipk.ck, &r_c, r_c_blinder).unwrap());

            // Commit to z_a ○ r_b + z_b ○ r_a.
            let z_a_times_r_b = cfg_iter!(z_a).zip(&r_b);
            let z_b_times_r_a = cfg_iter!(z_b).zip(&r_a);
            let cross_product: Vec<_> = z_a_times_r_b.zip(z_b_times_r_a).map(|((z_a, r_b), (z_b, r_a))| *z_a * r_b + *z_b * r_a).collect();
            blinder_1 = Some(G::ScalarField::rand(rng));
            comm_1 = Some(PedersenCommitment::commit(&ipk.ck, &cross_product, blinder_1).unwrap());

            // Commit to r_a ○ r_b.
            let r_a_r_b_product: Vec<_> = cfg_iter!(r_a).zip(r_b).map(|(r_a, r_b)| r_b * r_a).collect();
            blinder_2 = Some(G::ScalarField::rand(rng));
            comm_2 = Some(PedersenCommitment::commit(&ipk.ck, &r_a_r_b_product, blinder_2).unwrap());
        }
        let mut sponge = S::new();
        sponge.absorb(&ipk.index_info.matrices_hash.as_ref());
        let input_bytes = input.iter().flat_map(|inp| inp.into_repr().to_bytes_le()).collect::<Vec<_>>();
        sponge.absorb(&input_bytes);
        absorb![
            &mut sponge,
            &comm_a.0.to_field_elements().unwrap(),
            &comm_b.0.to_field_elements().unwrap(),
            &comm_c.0.to_field_elements().unwrap()
        ];
        if make_zk {
            absorb![
                &mut sponge,
                &comm_r_a.unwrap().0.to_field_elements().unwrap(),
                &comm_r_b.unwrap().0.to_field_elements().unwrap(),
                &comm_r_c.unwrap().0.to_field_elements().unwrap(),
                &comm_1.unwrap().0.to_field_elements().unwrap(),
                &comm_2.unwrap().0.to_field_elements().unwrap()
            ];
        }
        let gamma: G::ScalarField = sponge.squeeze_nonnative_field_elements_with_sizes(&[FieldElementSize::Truncated {
            num_bits: 128,
        }])[0];

        let mut blinded_witness = witness;
        let (mut sigma_a, mut sigma_b, mut sigma_c) = (None, None, None);
        let mut sigma_o = None;
        if make_zk {
            ark_std::cfg_iter_mut!(blinded_witness).zip(r.unwrap()).for_each(|(s, r)| *s += gamma * r);
            sigma_a = a_blinder.map(|a_blinder| a_blinder + gamma * r_a_blinder.unwrap());
            sigma_b = b_blinder.map(|b_blinder| b_blinder + gamma * r_b_blinder.unwrap());
            sigma_c = c_blinder.map(|c_blinder| c_blinder + gamma * r_c_blinder.unwrap());
            sigma_o = c_blinder.map(|c_blinder| c_blinder + gamma * blinder_1.unwrap() + gamma.square() * blinder_2.unwrap());
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
        let second_msg = SecondRoundMessage {
            blinded_witness,
            sigma_a,
            sigma_b,
            sigma_c,
            sigma_o,
        };

        let proof = Proof { first_msg, second_msg };
        end_timer!(init_time);
        Ok(proof)
    }

    pub fn verify() {

    }
}