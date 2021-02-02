use crate::data_structures::{Accumulator, AccumulatorRef, Input, InputRef};
use crate::error::{ASError, BoxedError};
use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
    InputWitnessRandomness as HPInputWitnessRandomness,
};
use crate::hp_as::HPAidedAccumulationScheme;
use crate::r1cs_nark::data_structures::{FirstRoundMessage, SecondRoundMessage};
use crate::r1cs_nark::{hash_matrices, matrix_vec_mul, PROTOCOL_NAME as NARK_PROTOCOL_NAME};
use crate::std::UniformRand;
use crate::AidedAccumulationScheme;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{One, Zero};
use ark_ff::{PrimeField, ToConstraintField};
use ark_poly_commit::pedersen::PedersenCommitment;
use ark_sponge::{CryptographicSponge, Absorbable};
use rand_core::RngCore;
use std::marker::PhantomData;

pub mod data_structures;
use data_structures::*;

pub(crate) const PROTOCOL_NAME: &[u8] = b"Simple-R1CS-NARK-Accumulation-Scheme-2020";

pub struct NARKVerifierAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField + Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    _affine: PhantomData<G>,
    _cf: PhantomData<CF>,
    _sponge: PhantomData<S>,
}

impl<G, CF, S> NARKVerifierAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField + Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    fn compute_prover_randomness(
        prover_key: &ProverKey<G>,
        rng: &mut dyn RngCore,
        r1cs_input_len: usize,
        r1cs_blinded_witness_len: usize,
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
        let r1cs_r_witness = vec![G::ScalarField::rand(rng); r1cs_blinded_witness_len];

        let rand_1 = G::ScalarField::rand(rng);
        let rand_2 = G::ScalarField::rand(rng);
        let rand_3 = G::ScalarField::rand(rng);

        let a = &prover_key.a;
        let b = &prover_key.b;
        let c = &prover_key.c;

        let comm_r_a = PedersenCommitment::commit(
            &prover_key.ck,
            (matrix_vec_mul(a, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_1),
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_r_b = PedersenCommitment::commit(
            &prover_key.ck,
            (matrix_vec_mul(b, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_2),
        )
        .map_err(BoxedError::new)?
        .0;

        let comm_r_c = PedersenCommitment::commit(
            &prover_key.ck,
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

    fn compute_hp_input_instances<'a>(
        input_instances: &Vec<&InputInstance<G>>,
    ) -> Vec<HPInputInstance<G>> {
        input_instances
            .into_iter()
            .map(|instance| {
                // Instantiate hp instances
                // TODO: Challenge
                let challenge = G::ScalarField::one();
                let first_round_message: &FirstRoundMessage<G> = &instance.first_round_message;

                let mut comm_1 = first_round_message.comm_a;
                let mut comm_2 = first_round_message.comm_b;
                let mut comm_3 = first_round_message.comm_c;

                if instance.make_zk {
                    let mut comm_1_proj = comm_1.into_projective();
                    let mut comm_2_proj = comm_2.into_projective();
                    let mut comm_3_proj = comm_3.into_projective();

                    if let Some(comm_r_a) = first_round_message.comm_r_a.as_ref() {
                        comm_1_proj += &comm_r_a.mul(challenge);
                    }

                    if let Some(comm_r_b) = first_round_message.comm_r_b.as_ref() {
                        comm_2_proj += &comm_r_b.mul(challenge);
                    }

                    if let Some(comm_r_c) = first_round_message.comm_r_c.as_ref() {
                        comm_3_proj += &comm_r_c.mul(challenge);
                    }

                    let mut comms = G::Projective::batch_normalization_into_affine(&[
                        comm_3_proj,
                        comm_2_proj,
                        comm_1_proj,
                    ]);
                    comm_1 = comms.pop().unwrap();
                    comm_2 = comms.pop().unwrap();
                    comm_3 = comms.pop().unwrap();
                }

                HPInputInstance {
                    comm_1,
                    comm_2,
                    comm_3,
                }
            })
            .collect::<Vec<_>>()
    }

    fn compute_hp_input_witnesses<'a>(
        prover_key: &ProverKey<G>,
        input_witnesses: &Vec<&InputWitness<G::ScalarField>>,
    ) -> Vec<HPInputWitness<G::ScalarField>> {
        input_witnesses
            .into_iter()
            .map(|witness| {
                let second_round_message: &SecondRoundMessage<G::ScalarField> =
                    &witness.second_round_message;
                let a_vec = matrix_vec_mul(
                    &prover_key.a,
                    second_round_message.blinded_witness.as_slice(),
                    &[],
                );
                let b_vec = matrix_vec_mul(
                    &prover_key.b,
                    second_round_message.blinded_witness.as_slice(),
                    &[],
                );

                let randomness = if witness.make_zk {
                    let rand_1 = second_round_message
                        .sigma_a
                        .unwrap_or(G::ScalarField::zero());
                    let rand_2 = second_round_message
                        .sigma_b
                        .unwrap_or(G::ScalarField::zero());
                    let rand_3 = second_round_message
                        .sigma_c
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

    fn compute_accumulator_instance_components(
        input_instances: &Vec<&InputInstance<G>>,
        accumulator_instances: &Vec<&AccumulatorInstance<G>>,
        linear_combination_challenges: &Vec<G::ScalarField>,
        proof_randomness: Option<&ProofRandomness<G>>,
    ) -> (Vec<G::ScalarField>, G, G, G) {
        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if proof_randomness.is_some() { 1 } else { 0 };
        assert!(num_addends <= linear_combination_challenges.len());

        let r1cs_inputs = accumulator_instances
            .iter()
            .map(|instance| &instance.r1cs_input)
            .chain(input_instances.iter().map(|instance| &instance.r1cs_input));

        let all_comm_a = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_a)
            .chain(
                input_instances
                    .iter()
                    .map(|instance| &instance.first_round_message.comm_a),
            );

        let all_comm_b = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_b)
            .chain(
                input_instances
                    .iter()
                    .map(|instance| &instance.first_round_message.comm_b),
            );

        let all_comm_c = accumulator_instances
            .iter()
            .map(|instance| &instance.comm_c)
            .chain(
                input_instances
                    .iter()
                    .map(|instance| &instance.first_round_message.comm_c),
            );

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

        let combined_r1cs_input = HPAidedAccumulationScheme::<G, CF, S>::combine_vectors(
            r1cs_inputs,
            linear_combination_challenges,
        );

        let combined_comm_a_proj = HPAidedAccumulationScheme::<G, CF, S>::combine_commitments(
            all_comm_a,
            linear_combination_challenges,
        );

        let combined_comm_b_proj = HPAidedAccumulationScheme::<G, CF, S>::combine_commitments(
            all_comm_b,
            linear_combination_challenges,
        );

        let combined_comm_c_proj = HPAidedAccumulationScheme::<G, CF, S>::combine_commitments(
            all_comm_c,
            linear_combination_challenges,
        );

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
        linear_combination_challenges: &Vec<G::ScalarField>,
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

        assert!(num_addends <= linear_combination_challenges.len());

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

        let combined_r1cs_blinded_witness = HPAidedAccumulationScheme::<G, CF, S>::combine_vectors(
            r1cs_blinded_witnesses,
            linear_combination_challenges,
        );

        let witness_randomness = if prover_witness_randomness.is_some() {
            let combined_sigma_a = HPAidedAccumulationScheme::<G, CF, S>::combine_randomness(
                all_sigma_a,
                linear_combination_challenges,
            );

            let combined_sigma_b = HPAidedAccumulationScheme::<G, CF, S>::combine_randomness(
                all_sigma_b,
                linear_combination_challenges,
            );

            let combined_sigma_c = HPAidedAccumulationScheme::<G, CF, S>::combine_randomness(
                all_sigma_c,
                linear_combination_challenges,
            );

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

impl<G, CF, S> AidedAccumulationScheme for NARKVerifierAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField + Absorbable<CF>,
    S: CryptographicSponge<CF>,
{
    type UniversalParams =
        <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::UniversalParams;

    type PredicateParams = ();
    type PredicateIndex = PredicateIndex<G::ScalarField>;

    type ProverKey = ProverKey<G>;
    type VerifierKey = VerifierKey;
    type DeciderKey = DeciderKey<G>;
    type InputInstance = InputInstance<G>;
    type InputWitness = InputWitness<G::ScalarField>;
    type AccumulatorInstance = AccumulatorInstance<G>;
    type AccumulatorWitness = AccumulatorWitness<G::ScalarField>;
    type Proof = Proof<G>;
    type Error = BoxedError;

    fn generate(rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::generate(rng)
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        _predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let a = predicate_index.a.clone();
        let b = predicate_index.b.clone();
        let c = predicate_index.c.clone();

        let nark_matrices_hash = hash_matrices(NARK_PROTOCOL_NAME, &a, &b, &c);
        let as_matrices_hash = hash_matrices(PROTOCOL_NAME, &a, &b, &c);
        let index = predicate_index.index;

        let ped_pp = PedersenCommitment::setup(index).map_err(BoxedError::new)?;
        let ck = PedersenCommitment::trim(&ped_pp, index).map_err(BoxedError::new)?;

        let pk = ProverKey {
            a: a.clone(),
            b: b.clone(),
            c: c.clone(),
            as_matrices_hash,
            nark_matrices_hash,
            index,
            ck: ck.clone(),
        };

        let vk = VerifierKey {
            as_matrices_hash,
            nark_matrices_hash,
            index,
        };

        let dk = DeciderKey { a, b, c, index, ck };

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
        let mut r1cs_input_len = 0;
        let mut r1cs_blinded_witness_len = 0;

        let mut accumulator_instances = Vec::new();
        let mut accumulator_witnesses = Vec::new();
        for acc in accumulators {
            let instance = acc.instance;
            let witness = acc.witness;

            make_zk = make_zk || witness.randomness.is_some();
            r1cs_input_len = r1cs_input_len.max(instance.r1cs_input.len());
            r1cs_blinded_witness_len =
                r1cs_blinded_witness_len.max(witness.r1cs_blinded_witness.len());

            accumulator_instances.push(instance);
            accumulator_witnesses.push(witness);
        }

        let mut input_instances = Vec::new();
        let mut input_witnesses = Vec::new();
        for input in inputs {
            let instance = input.instance;
            let witness = input.witness;
            let second_round_message = &witness.second_round_message;

            make_zk = make_zk || instance.make_zk || witness.make_zk;
            r1cs_input_len = r1cs_input_len.max(instance.r1cs_input.len());
            r1cs_blinded_witness_len =
                r1cs_blinded_witness_len.max(second_round_message.blinded_witness.len());

            input_instances.push(instance);
            input_witnesses.push(witness);
        }

        let num_addends =
            input_instances.len() + accumulator_instances.len() + if make_zk { 1 } else { 0 };

        // Run HP AS
        let combined_hp_input_instances = Self::compute_hp_input_instances(&input_instances);
        let combined_hp_input_witnesses =
            Self::compute_hp_input_witnesses(prover_key, &input_witnesses);

        let combined_hp_inputs_iter = combined_hp_input_instances
            .iter()
            .zip(&combined_hp_input_witnesses)
            .map(
                |(instance, witness)| InputRef::<HPAidedAccumulationScheme<_, _, S>> {
                    instance,
                    witness,
                },
            );

        let hp_accumulators_iter = accumulator_instances
            .iter()
            .zip(&accumulator_witnesses)
            .map(
                |(instance, witness)| AccumulatorRef::<HPAidedAccumulationScheme<_, _, S>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            );

        let (hp_accumulator, hp_proof) = HPAidedAccumulationScheme::<_, _, S>::prove(
            &prover_key.ck,
            combined_hp_inputs_iter,
            hp_accumulators_iter,
            Some(*rng.as_mut().unwrap()),
        )?;

        let (proof_randomness, prover_witness_randomness) = if make_zk {
            let rng = rng.ok_or(BoxedError::new(ASError::MissingRng(
                "Accumulating inputs with hiding requires rng.".to_string(),
            )))?;

            let (proof_randomness, prover_witness_randomness) = Self::compute_prover_randomness(
                prover_key,
                rng,
                r1cs_input_len,
                r1cs_blinded_witness_len,
            )?;

            (Some(proof_randomness), Some(prover_witness_randomness))
        } else {
            (None, None)
        };

        // TODO: Challenge
        // TODO: Can these challenges be independent challenges?
        let linear_combination_challenge = G::ScalarField::one() + G::ScalarField::one();
        let mut linear_combination_challenges = Vec::with_capacity(num_addends);
        let mut cur_challenge = G::ScalarField::one();
        for _ in 0..num_addends {
            linear_combination_challenges.push(cur_challenge);
            cur_challenge *= linear_combination_challenge;
        }

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &accumulator_instances,
            &linear_combination_challenges,
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
            &linear_combination_challenges,
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

        let linear_combination_challenge = G::ScalarField::one() + G::ScalarField::one();
        let mut linear_combination_challenges = Vec::with_capacity(num_addends);
        let mut cur_challenge = G::ScalarField::one();
        for _ in 0..num_addends {
            linear_combination_challenges.push(cur_challenge);
            cur_challenge *= linear_combination_challenge;
        }

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &accumulator_instances,
            &linear_combination_challenges,
            proof.randomness.as_ref(),
        );

        let hp_input_instances = Self::compute_hp_input_instances(&input_instances);
        let hp_accumulator_instances = accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        // TODO: Replace with proper vk
        let hp_verify = HPAidedAccumulationScheme::<_, _, S>::verify(
            &(),
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
        )?;

        return Ok(hp_verify
            && r1cs_input.eq(&new_accumulator_instance.r1cs_input)
            && comm_a.eq(&new_accumulator_instance.comm_a)
            && comm_b.eq(&new_accumulator_instance.comm_b)
            && comm_c.eq(&new_accumulator_instance.comm_c));
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<Self>,
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
            && HPAidedAccumulationScheme::<_, _, S>::decide(
                &decider_key.ck,
                AccumulatorRef::<HPAidedAccumulationScheme<_, _, S>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            )?)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::r1cs_nark_as::NARKVerifierAidedAccumulationScheme;
    use crate::tests::*;
    use crate::AidedAccumulationScheme;
    use crate::Input;
    use ark_ec::AffineCurve;
    use ark_ff::{ToConstraintField, PrimeField};
    use ark_sponge::{CryptographicSponge, Absorbable};
    use crate::error::BoxedError;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq};
    use ark_sponge::poseidon::PoseidonSponge;
    use rand_core::RngCore;

    pub struct NARKVerifierAidedAccumulationSchemeTestInput {}

    impl<G, CF, S> AccumulationSchemeTestInput<NARKVerifierAidedAccumulationScheme<G, CF, S>>
    for NARKVerifierAidedAccumulationSchemeTestInput
        where
            G: AffineCurve + ToConstraintField<CF>,
            CF: PrimeField + Absorbable<CF>,
            S: CryptographicSponge<CF>,
    {
        type TestParams = ();
        type InputParams = ();

        fn setup(
            test_params: &Self::TestParams,
            _rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <NARKVerifierAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::PredicateParams,
            <NARKVerifierAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::PredicateIndex,
        ) {
            unimplemented!()
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            _rng: &mut impl RngCore,
        ) -> Vec<Input<NARKVerifierAidedAccumulationScheme<G, CF, S>>> {
            unimplemented!()
        }
    }

    type AS = NARKVerifierAidedAccumulationScheme<EdwardsAffine, Fq, PoseidonSponge<Fq>>;

    type I = NARKVerifierAidedAccumulationSchemeTestInput;

    /*
    #[test]
    pub fn nv_single_input_test() -> Result<(), BoxedError> {
        single_input_test::<AS, I>(&())
    }

    #[test]
    pub fn nv_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_inputs_test::<AS, I>(&(8, false))
    }

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

