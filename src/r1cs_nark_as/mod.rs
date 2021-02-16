use crate::constraints::ConstraintF;
use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
    InputWitnessRandomness as HPInputWitnessRandomness,
};
use crate::hp_as::HPSplitAS;
use crate::r1cs_nark::data_structures::{
    FirstRoundMessage, IndexInfo, IndexVerifierKey, PublicParameters as NARKPublicParameters,
    SecondRoundMessage,
};
use crate::r1cs_nark::{hash_matrices, matrix_vec_mul, SimpleNARK};
use crate::std::UniformRand;
use crate::SplitAccumulationScheme;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::ToConstraintField;
use ark_ff::{One, Zero};
use ark_poly_commit::pedersen::PedersenCommitment;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_sponge::{Absorbable, CryptographicSponge, DomainSeparatedSponge, FieldElementSize};
use rand_core::RngCore;
use std::marker::PhantomData;

pub mod data_structures;
use data_structures::*;

pub mod constraints;

pub(crate) const PROTOCOL_NAME: &[u8] = b"Simple-R1CS-NARK-Accumulation-Scheme-2020";

pub struct SimpleNARKSplitAS<G, CS, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
    _constraint_synthesizer: PhantomData<CS>,
}

impl<G, CS, S> SimpleNARKSplitAS<G, CS, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    fn compute_blinded_commitments(
        index_info: &IndexInfo,
        input_instances: &Vec<&InputInstance<G>>,
    ) -> (Vec<G>, Vec<G>, Vec<G>, Vec<G>) {
        let mut all_blinded_comm_a = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_b = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_c = Vec::with_capacity(input_instances.len());
        let mut all_blinded_comm_prod = Vec::with_capacity(input_instances.len());

        for instance in input_instances {
            let first_round_message: &FirstRoundMessage<G> = &instance.first_round_message;

            let mut comm_a = first_round_message.comm_a;
            let mut comm_b = first_round_message.comm_b;
            let mut comm_c = first_round_message.comm_c;
            let mut comm_prod = first_round_message.comm_c;

            if instance.make_zk {
                let gamma_challenge = SimpleNARK::<
                    G,
                    DomainSeparatedSponge<ConstraintF<G>, S, SimpleNARKDomain>,
                >::compute_challenge(
                    index_info,
                    instance.r1cs_input.as_slice(),
                    first_round_message,
                );

                let mut comm_a_proj = comm_a.into_projective();
                let mut comm_b_proj = comm_b.into_projective();
                let mut comm_c_proj = comm_c.into_projective();
                let mut comm_prod_proj = comm_prod.into_projective();

                if let Some(comm_r_a) = first_round_message.comm_r_a.as_ref() {
                    comm_a_proj += &comm_r_a.mul(gamma_challenge);
                }

                if let Some(comm_r_b) = first_round_message.comm_r_b.as_ref() {
                    comm_b_proj += &comm_r_b.mul(gamma_challenge);
                }

                if let Some(comm_r_c) = first_round_message.comm_r_c.as_ref() {
                    comm_c_proj += &comm_r_c.mul(gamma_challenge);
                }

                if let Some(comm_1) = first_round_message.comm_1.as_ref() {
                    comm_prod_proj += &comm_1.mul(gamma_challenge);
                }

                if let Some(comm_2) = first_round_message.comm_2.as_ref() {
                    comm_prod_proj += &comm_2.mul(gamma_challenge * &gamma_challenge);
                }

                let mut comms = G::Projective::batch_normalization_into_affine(&[
                    comm_prod_proj,
                    comm_c_proj,
                    comm_b_proj,
                    comm_a_proj,
                ]);

                comm_a = comms.pop().unwrap();
                comm_b = comms.pop().unwrap();
                comm_c = comms.pop().unwrap();
                comm_prod = comms.pop().unwrap();
            }

            all_blinded_comm_a.push(comm_a);
            all_blinded_comm_b.push(comm_b);
            all_blinded_comm_c.push(comm_c);
            all_blinded_comm_prod.push(comm_prod);
        }

        (
            all_blinded_comm_a,
            all_blinded_comm_b,
            all_blinded_comm_c,
            all_blinded_comm_prod,
        )
    }

    fn compute_hp_input_instances(
        all_blinded_comm_a: &Vec<G>,
        all_blinded_comm_b: &Vec<G>,
        all_blinded_comm_prod: &Vec<G>,
    ) -> Vec<HPInputInstance<G>> {
        assert!(
            all_blinded_comm_a.len() == all_blinded_comm_b.len()
                && all_blinded_comm_b.len() == all_blinded_comm_prod.len()
        );

        let mut input_instances = Vec::with_capacity(all_blinded_comm_a.len());
        all_blinded_comm_a
            .into_iter()
            .zip(all_blinded_comm_b)
            .zip(all_blinded_comm_prod)
            .for_each(|((comm_a, comm_b), comm_prod)| {
                input_instances.push(HPInputInstance {
                    comm_1: comm_a.clone(),
                    comm_2: comm_b.clone(),
                    comm_3: comm_prod.clone(),
                });
            });

        input_instances
    }

    fn compute_hp_input_witnesses<'a>(
        prover_key: &ProverKey<G>,
        inputs: &Vec<InputRef<'_, Self>>,
    ) -> Vec<HPInputWitness<G::ScalarField>> {
        inputs
            .into_iter()
            .map(|input| {
                let instance = input.instance;
                let witness = input.witness;

                let second_round_message: &SecondRoundMessage<G::ScalarField> =
                    &witness.second_round_message;

                let a_vec = matrix_vec_mul(
                    &prover_key.nark_pk.a,
                    instance.r1cs_input.as_slice(),
                    second_round_message.blinded_witness.as_slice(),
                );

                let b_vec = matrix_vec_mul(
                    &prover_key.nark_pk.b,
                    instance.r1cs_input.as_slice(),
                    second_round_message.blinded_witness.as_slice(),
                );

                let randomness = if witness.make_zk {
                    let rand_1 = second_round_message
                        .sigma_a
                        .unwrap_or(G::ScalarField::zero());
                    let rand_2 = second_round_message
                        .sigma_b
                        .unwrap_or(G::ScalarField::zero());
                    let rand_3 = second_round_message
                        .sigma_o
                        .unwrap_or(G::ScalarField::zero());

                    Some(HPInputWitnessRandomness::<G::ScalarField> {
                        rand_1,
                        rand_2,
                        rand_3,
                    })
                } else {
                    None
                };

                HPInputWitness {
                    a_vec,
                    b_vec,
                    randomness,
                }
            })
            .collect::<Vec<_>>()
    }

    fn compute_prover_randomness(
        prover_key: &ProverKey<G>,
        rng: &mut dyn RngCore,
        r1cs_input_len: usize,
        r1cs_witness_len: usize,
    ) -> Result<
        (
            ProofRandomness<G>,
            (
                Vec<G::ScalarField>, // r_witness
                G::ScalarField,      // sigma_a
                G::ScalarField,      // sigma_b
                G::ScalarField,      // sigma_c
            ),
        ),
        BoxedError,
    > {
        let r1cs_r_input = vec![G::ScalarField::rand(rng); r1cs_input_len];
        let r1cs_r_witness = vec![G::ScalarField::rand(rng); r1cs_witness_len];

        let rand_1 = G::ScalarField::rand(rng);
        let rand_2 = G::ScalarField::rand(rng);
        let rand_3 = G::ScalarField::rand(rng);

        let a = &prover_key.nark_pk.a;
        let b = &prover_key.nark_pk.b;
        let c = &prover_key.nark_pk.c;

        let comm_r_a = PedersenCommitment::commit(
            &prover_key.nark_pk.ck,
            (matrix_vec_mul(a, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_1),
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_r_b = PedersenCommitment::commit(
            &prover_key.nark_pk.ck,
            (matrix_vec_mul(b, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_2),
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_r_c = PedersenCommitment::commit(
            &prover_key.nark_pk.ck,
            (matrix_vec_mul(c, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_3),
        )
        .map_err(BoxedError::new)?
        .0;

        let proof_randomness = ProofRandomness {
            r1cs_r_input,
            comm_r_a,
            comm_r_b,
            comm_r_c,
        };

        Ok((proof_randomness, (r1cs_r_witness, rand_1, rand_2, rand_3)))
    }

    fn compute_beta_challenges(
        num_challenges: usize,
        as_matrices_hash: &[u8; 32],
        accumulator_instances: &Vec<&AccumulatorInstance<G>>,
        input_instances: &Vec<&InputInstance<G>>,
        proof_randomness: &Option<ProofRandomness<G>>,
    ) -> Vec<G::ScalarField> {
        let mut sponge =
            DomainSeparatedSponge::<ConstraintF<G>, S, SimpleNARKVerifierASDomain>::new();

        sponge.absorb(&as_matrices_hash.as_ref());

        for acc_instance in accumulator_instances {
            sponge.absorb(acc_instance);
        }

        for input_instance in input_instances {
            sponge.absorb(input_instance);
        }

        sponge.absorb(proof_randomness);

        let mut squeeze = sponge.squeeze_nonnative_field_elements_with_sizes(
            vec![FieldElementSize::Truncated { num_bits: 128 }; num_challenges - 1].as_slice(),
        );

        let mut outputs = Vec::with_capacity(num_challenges);
        outputs.push(G::ScalarField::one());
        outputs.append(&mut squeeze);

        outputs
    }

    fn compute_accumulator_instance_components(
        input_instances: &Vec<&InputInstance<G>>,
        all_blinded_comm_a: &Vec<G>,
        all_blinded_comm_b: &Vec<G>,
        all_blinded_comm_c: &Vec<G>,
        accumulator_instances: &Vec<&AccumulatorInstance<G>>,
        beta_challenges: &Vec<G::ScalarField>,
        proof_randomness: Option<&ProofRandomness<G>>,
    ) -> (Vec<G::ScalarField>, G, G, G) {
        assert!(
            input_instances.len() == all_blinded_comm_a.len()
                && all_blinded_comm_a.len() == all_blinded_comm_b.len()
                && all_blinded_comm_b.len() == all_blinded_comm_c.len()
        );

        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if proof_randomness.is_some() { 1 } else { 0 };

        assert!(num_addends <= beta_challenges.len());

        let r1cs_inputs = accumulator_instances
            .iter()
            .map(|instance| &instance.r1cs_input)
            .chain(input_instances.iter().map(|instance| &instance.r1cs_input));

        let all_comm_a = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_a)
            .chain(all_blinded_comm_a);

        let all_comm_b = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_b)
            .chain(all_blinded_comm_b);

        let all_comm_c = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_c)
            .chain(all_blinded_comm_c);

        let (r1cs_inputs, all_comm_a, all_comm_b, all_comm_c) = if proof_randomness.is_some() {
            (
                r1cs_inputs.chain(vec![&proof_randomness.as_ref().unwrap().r1cs_r_input]),
                all_comm_a.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_a]),
                all_comm_b.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_b]),
                all_comm_c.chain(vec![&proof_randomness.as_ref().unwrap().comm_r_c]),
            )
        } else {
            (
                r1cs_inputs.chain(vec![]),
                all_comm_a.chain(vec![]),
                all_comm_b.chain(vec![]),
                all_comm_c.chain(vec![]),
            )
        };

        let combined_r1cs_input =
            HPSplitAS::<G, S>::combine_vectors(r1cs_inputs, beta_challenges, None);

        let combined_comm_a_proj =
            HPSplitAS::<G, S>::combine_commitments(all_comm_a, beta_challenges, None);

        let combined_comm_b_proj =
            HPSplitAS::<G, S>::combine_commitments(all_comm_b, beta_challenges, None);

        let combined_comm_c_proj =
            HPSplitAS::<G, S>::combine_commitments(all_comm_c, beta_challenges, None);

        let mut combined_comms = G::Projective::batch_normalization_into_affine(&[
            combined_comm_c_proj,
            combined_comm_b_proj,
            combined_comm_a_proj,
        ]);

        let combined_comm_a = combined_comms.pop().unwrap();
        let combined_comm_b = combined_comms.pop().unwrap();
        let combined_comm_c = combined_comms.pop().unwrap();

        (
            combined_r1cs_input,
            combined_comm_a,
            combined_comm_b,
            combined_comm_c,
        )
    }

    fn compute_accumulator_witness_components(
        input_witnesses: &Vec<&InputWitness<G::ScalarField>>,
        accumulator_witnesses: &Vec<&AccumulatorWitness<G::ScalarField>>,
        beta_challenges: &Vec<G::ScalarField>,
        prover_witness_randomness: Option<&(
            Vec<G::ScalarField>, // r_witness
            G::ScalarField,      // sigma_a
            G::ScalarField,      // sigma_b
            G::ScalarField,      // sigma_c
        )>,
    ) -> (
        Vec<G::ScalarField>,
        Option<AccumulatorWitnessRandomness<G::ScalarField>>,
    ) {
        let num_addends = input_witnesses.len()
            + accumulator_witnesses.len()
            + if prover_witness_randomness.is_some() {
                1
            } else {
                0
            };

        assert!(num_addends <= beta_challenges.len());

        let r1cs_blinded_witnesses = accumulator_witnesses
            .iter()
            .map(|witness| &witness.r1cs_blinded_witness)
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| &witness.second_round_message.blinded_witness),
            );

        let all_sigma_a = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_a))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.second_round_message.sigma_a.as_ref()),
            );

        let all_sigma_b = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_b))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.second_round_message.sigma_b.as_ref()),
            );

        let all_sigma_c = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_c))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.second_round_message.sigma_c.as_ref()),
            );

        let (r1cs_blinded_witnesses, all_sigma_a, all_sigma_b, all_sigma_c) =
            if let Some((r1cs_r_witness, rand_1, rand_2, rand_3)) = prover_witness_randomness {
                (
                    r1cs_blinded_witnesses.chain(vec![r1cs_r_witness]),
                    all_sigma_a.chain(vec![Some(rand_1)]),
                    all_sigma_b.chain(vec![Some(rand_2)]),
                    all_sigma_c.chain(vec![Some(rand_3)]),
                )
            } else {
                (
                    r1cs_blinded_witnesses.chain(vec![]),
                    all_sigma_a.chain(vec![]),
                    all_sigma_b.chain(vec![]),
                    all_sigma_c.chain(vec![]),
                )
            };

        let combined_r1cs_blinded_witness =
            HPSplitAS::<G, S>::combine_vectors(r1cs_blinded_witnesses, beta_challenges, None);

        let witness_randomness = if prover_witness_randomness.is_some() {
            let combined_sigma_a =
                HPSplitAS::<G, S>::combine_randomness(all_sigma_a, beta_challenges, None);

            let combined_sigma_b =
                HPSplitAS::<G, S>::combine_randomness(all_sigma_b, beta_challenges, None);

            let combined_sigma_c =
                HPSplitAS::<G, S>::combine_randomness(all_sigma_c, beta_challenges, None);

            Some(AccumulatorWitnessRandomness {
                sigma_a: combined_sigma_a,
                sigma_b: combined_sigma_b,
                sigma_c: combined_sigma_c,
            })
        } else {
            None
        };

        (combined_r1cs_blinded_witness, witness_randomness)
    }
}

impl<G, CS, S> SplitAccumulationScheme for SimpleNARKSplitAS<G, CS, S>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    type UniversalParams = <HPSplitAS<G, S> as SplitAccumulationScheme>::UniversalParams;

    type PredicateParams = NARKPublicParameters;
    type PredicateIndex = CS;

    type ProverKey = ProverKey<G>;
    type VerifierKey = VerifierKey;
    type DeciderKey = IndexVerifierKey<G>;
    type InputInstance = InputInstance<G>;
    type InputWitness = InputWitness<G::ScalarField>;
    type AccumulatorInstance = AccumulatorInstance<G>;
    type AccumulatorWitness = AccumulatorWitness<G::ScalarField>;
    type Proof = Proof<G>;
    type Error = BoxedError;

    fn generate(rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        <HPSplitAS<G, S> as SplitAccumulationScheme>::generate(rng)
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ipk, ivk) =
            SimpleNARK::<G, DomainSeparatedSponge<ConstraintF<G>, S, SimpleNARKDomain>>::index(
                &predicate_params,
                predicate_index.clone(),
            )
            .map_err(BoxedError::new)?;

        let as_matrices_hash = hash_matrices(PROTOCOL_NAME, &ipk.a, &ipk.b, &ipk.c);

        let pk = ProverKey {
            nark_pk: ipk,
            as_matrices_hash: as_matrices_hash.clone(),
        };

        let vk = VerifierKey {
            nark_index: ivk.index_info.clone(),
            as_matrices_hash,
        };

        let dk = ivk;

        Ok((pk, vk, dk))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, Self>>,
        accumulators: impl IntoIterator<Item = AccumulatorRef<'a, Self>>,
        mut rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        // Collect all of the inputs and accumulators into vectors and extract additional information from them.
        let mut make_zk = false;

        let mut accumulator_instances = Vec::new();
        let mut accumulator_witnesses = Vec::new();
        for acc in accumulators {
            let instance = acc.instance;
            let witness = acc.witness;

            make_zk = make_zk || witness.randomness.is_some();
            accumulator_instances.push(instance);
            accumulator_witnesses.push(witness);
        }

        let mut all_inputs = Vec::new();
        let mut input_instances = Vec::new();
        let mut input_witnesses = Vec::new();
        for input in inputs {
            let instance = input.instance;
            let witness = input.witness;

            make_zk = make_zk || instance.make_zk || witness.make_zk;
            input_instances.push(instance);
            input_witnesses.push(witness);
            all_inputs.push(input);
        }

        let num_addends =
            input_instances.len() + accumulator_instances.len() + if make_zk { 1 } else { 0 };

        // Run HP AS
        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(&prover_key.nark_pk.index_info, &input_instances);

        let combined_hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );
        let combined_hp_input_witnesses = Self::compute_hp_input_witnesses(prover_key, &all_inputs);

        let combined_hp_inputs_iter = combined_hp_input_instances
            .iter()
            .zip(&combined_hp_input_witnesses)
            .map(|(instance, witness)| InputRef::<HPSplitAS<_, S>> { instance, witness });

        let hp_accumulators_iter = accumulator_instances
            .iter()
            .zip(&accumulator_witnesses)
            .map(|(instance, witness)| AccumulatorRef::<HPSplitAS<_, S>> {
                instance: &instance.hp_instance,
                witness: &witness.hp_witness,
            });

        let (hp_accumulator, hp_proof) = HPSplitAS::<_, S>::prove(
            &prover_key.nark_pk.ck,
            combined_hp_inputs_iter,
            hp_accumulators_iter,
            Some(*rng.as_mut().unwrap()),
        )?;

        let (proof_randomness, prover_witness_randomness) = if make_zk {
            let rng = rng.ok_or(BoxedError::new(ASError::MissingRng(
                "Accumulating inputs with hiding requires rng.".to_string(),
            )))?;

            let index_info = &prover_key.nark_pk.index_info;
            let (proof_randomness, prover_witness_randomness) = Self::compute_prover_randomness(
                prover_key,
                rng,
                index_info.num_instance_variables,
                index_info.num_variables - index_info.num_instance_variables,
            )?;

            (Some(proof_randomness), Some(prover_witness_randomness))
        } else {
            (None, None)
        };

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &prover_key.as_matrices_hash,
            &accumulator_instances,
            &input_instances,
            &proof_randomness,
        );

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &accumulator_instances,
            &beta_challenges,
            proof_randomness.as_ref(),
        );

        let combined_acc_instance = AccumulatorInstance {
            r1cs_input,
            comm_a,
            comm_b,
            comm_c,
            hp_instance: hp_accumulator.instance.clone(),
        };

        let (r1cs_blinded_witness, randomness) = Self::compute_accumulator_witness_components(
            &input_witnesses,
            &accumulator_witnesses,
            &beta_challenges,
            prover_witness_randomness.as_ref(),
        );
        let combined_acc_witness = AccumulatorWitness {
            r1cs_blinded_witness,
            hp_witness: hp_accumulator.witness,
            randomness,
        };

        let accumulator = Accumulator::<Self> {
            instance: combined_acc_instance,
            witness: combined_acc_witness,
        };

        let proof = Proof {
            hp_proof,
            randomness: proof_randomness,
        };

        Ok((accumulator, proof))
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
        let input_instances = input_instances.into_iter().collect::<Vec<_>>();
        let accumulator_instances = accumulator_instances.into_iter().collect::<Vec<_>>();

        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if proof.randomness.is_some() { 1 } else { 0 };

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &verifier_key.as_matrices_hash,
            &accumulator_instances,
            &input_instances,
            &proof.randomness,
        );

        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(&verifier_key.nark_index, &input_instances);

        let hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        let hp_accumulator_instances = accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        let hp_verify = HPSplitAS::<_, S>::verify(
            &verifier_key.nark_index.num_constraints,
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
        )?;

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &accumulator_instances,
            &beta_challenges,
            proof.randomness.as_ref(),
        );

        Ok(hp_verify
            && r1cs_input.eq(&new_accumulator_instance.r1cs_input)
            && comm_a.eq(&new_accumulator_instance.comm_a)
            && comm_b.eq(&new_accumulator_instance.comm_b)
            && comm_c.eq(&new_accumulator_instance.comm_c))
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, Self>,
    ) -> Result<bool, Self::Error> {
        let instance = accumulator.instance;
        let witness = accumulator.witness;

        let a_times_blinded_witness = matrix_vec_mul(
            &decider_key.a,
            &instance.r1cs_input,
            &witness.r1cs_blinded_witness,
        );

        let b_times_blinded_witness = matrix_vec_mul(
            &decider_key.b,
            &instance.r1cs_input,
            &witness.r1cs_blinded_witness,
        );

        let c_times_blinded_witness = matrix_vec_mul(
            &decider_key.c,
            &instance.r1cs_input,
            &witness.r1cs_blinded_witness,
        );

        let (sigma_a, sigma_b, sigma_c) = if let Some(randomness) = witness.randomness.as_ref() {
            (
                Some(randomness.sigma_a),
                Some(randomness.sigma_b),
                Some(randomness.sigma_c),
            )
        } else {
            (None, None, None)
        };

        let comm_a = PedersenCommitment::commit(
            &decider_key.ck,
            a_times_blinded_witness.as_slice(),
            sigma_a,
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_b = PedersenCommitment::commit(
            &decider_key.ck,
            b_times_blinded_witness.as_slice(),
            sigma_b,
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_c = PedersenCommitment::commit(
            &decider_key.ck,
            c_times_blinded_witness.as_slice(),
            sigma_c,
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_check = comm_a.eq(&instance.comm_a)
            && comm_b.eq(&instance.comm_b)
            && comm_c.eq(&instance.comm_c);

        Ok(comm_check
            && HPSplitAS::<_, S>::decide(
                &decider_key.ck,
                AccumulatorRef::<HPSplitAS<_, S>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            )?)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ConstraintF;
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::r1cs_nark::data_structures::IndexProverKey;
    use crate::r1cs_nark::SimpleNARK;
    use crate::r1cs_nark_as::data_structures::{InputInstance, InputWitness, SimpleNARKDomain};
    use crate::r1cs_nark_as::SimpleNARKSplitAS;
    use crate::tests::*;
    use crate::SplitAccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq, Fr};
    use ark_ff::{PrimeField, ToConstraintField};
    use ark_relations::lc;
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
        SynthesisError,
    };
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge, DomainSeparatedSponge};
    use rand_core::RngCore;
    use std::UniformRand;

    #[derive(Clone)]
    // num_variables = num_inputs + 2
    pub struct NARKVerifierASTestParams {
        // At least one input required.
        pub num_inputs: usize,

        // At least one constraint required.
        pub num_constraints: usize,

        pub make_zk: bool,
    }

    #[derive(Clone)]
    pub(crate) struct DummyCircuit<F: PrimeField> {
        pub a: Option<F>,
        pub b: Option<F>,
        pub params: NARKVerifierASTestParams,
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

            for _ in 0..(self.params.num_inputs - 1) {
                cs.new_input_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..(self.params.num_constraints - 1) {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
            }

            cs.enforce_constraint(lc!(), lc!(), lc!())?;

            Ok(())
        }
    }

    pub struct SimpleNARKSplitASInput {}

    impl<G, S> SplitASTestInput<SimpleNARKSplitAS<G, DummyCircuit<G::ScalarField>, S>>
        for SimpleNARKSplitASInput
    where
        G: AffineCurve + ToConstraintField<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = NARKVerifierASTestParams;
        type InputParams = (Self::TestParams, IndexProverKey<G>);

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <SimpleNARKSplitAS<G, DummyCircuit<G::ScalarField>, S> as SplitAccumulationScheme>::PredicateParams,
            <SimpleNARKSplitAS<G, DummyCircuit<G::ScalarField>, S> as SplitAccumulationScheme>::PredicateIndex,
        ){
            let nark_pp =
                SimpleNARK::<G, DomainSeparatedSponge<ConstraintF<G>, S, SimpleNARKDomain>>::setup(
                );
            let _make_zk = test_params.make_zk;
            let circuit = DummyCircuit {
                a: Some(G::ScalarField::rand(rng)),
                b: Some(G::ScalarField::rand(rng)),
                params: test_params.clone(),
            };

            let (pk, _) =
                SimpleNARK::<G, DomainSeparatedSponge<ConstraintF<G>, S, SimpleNARKDomain>>::index(
                    &nark_pp,
                    circuit.clone(),
                )
                .unwrap();

            ((test_params.clone(), pk), nark_pp, circuit)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<SimpleNARKSplitAS<G, DummyCircuit<G::ScalarField>, S>>> {
            let (test_params, ipk) = input_params;

            let mut inputs = Vec::with_capacity(num_inputs);
            for _ in 0..num_inputs {
                let circuit = DummyCircuit {
                    a: Some(G::ScalarField::rand(rng)),
                    b: Some(G::ScalarField::rand(rng)),
                    params: input_params.0.clone(),
                };

                let proof = SimpleNARK::<
                    G,
                    DomainSeparatedSponge<ConstraintF<G>, S, SimpleNARKDomain>,
                >::prove(
                    ipk, circuit.clone(), test_params.make_zk, Some(rng)
                )
                .unwrap();

                let pcs = ConstraintSystem::new_ref();
                pcs.set_optimization_goal(OptimizationGoal::Weight);
                pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
                    construct_matrices: false,
                });
                circuit.generate_constraints(pcs.clone()).unwrap();
                pcs.finalize();
                let r1cs_input = pcs.borrow().unwrap().instance_assignment.clone();

                let instance = InputInstance {
                    r1cs_input: r1cs_input.clone(),
                    first_round_message: proof.first_msg.clone(),
                    make_zk: proof.make_zk,
                };

                let witness = InputWitness {
                    second_round_message: proof.second_msg,
                    make_zk: proof.make_zk,
                };

                inputs.push(
                    Input::<SimpleNARKSplitAS<G, DummyCircuit<G::ScalarField>, S>> {
                        instance,
                        witness,
                    },
                );
            }

            inputs
        }
    }

    type AS = SimpleNARKSplitAS<EdwardsAffine, DummyCircuit<Fr>, PoseidonSponge<Fq>>;

    type I = SimpleNARKSplitASInput;

    #[test]
    pub fn nv_single_input_test() -> Result<(), BoxedError> {
        single_input_test::<AS, I>(&NARKVerifierASTestParams {
            num_inputs: 10,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn nv_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_inputs_test::<AS, I>(&NARKVerifierASTestParams {
            num_inputs: 10,
            num_constraints: 10,
            make_zk: true,
        })
    }

    /*
    #[test]
    pub fn nv_multiple_accumulations_test() -> Result<(), BoxedError> {
        multiple_accumulations_test::<AS, I>(&8)
    }

    #[test]
    pub fn nv_multiple_accumulations_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_accumulations_multiple_inputs_test::<AS, I>(&8)
    }

    #[test]
    pub fn nv_accumulators_only_test() -> Result<(), BoxedError> {
        accumulators_only_test::<AS, I>(&8)
    }

     */
}
