use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::ASError::{MalformedAccumulator, MalformedInput};
use crate::error::{ASError, BoxedError};
use crate::hp_as::ASForHadamardProducts;
use crate::hp_as::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
    InputWitnessRandomness as HPInputWitnessRandomness,
};
use crate::r1cs_nark_as::r1cs_nark::{hash_matrices, matrix_vec_mul, R1CSNark};
use crate::ConstraintF;
use crate::{AccumulationScheme, MakeZK};

use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::One;
use ark_ff::UniformRand;
use ark_poly_commit::trivial_pc::PedersenCommitment;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;
use r1cs_nark::{
    FirstRoundMessage, IndexInfo, IndexVerifierKey, PublicParameters as NARKPublicParameters,
    SecondRoundMessage,
};
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

/// A simple non-interactive argument of knowledge for R1CS.
pub mod r1cs_nark;

/// The verifier constraints of [`ASForR1CSNark`].
#[cfg(feature = "r1cs")]
pub mod constraints;

pub(crate) const HP_AS_PROTOCOL_NAME: &[u8] = b"AS-FOR-HP-2020";
pub(crate) const PROTOCOL_NAME: &[u8] = b"AS-FOR-R1CS-NARK-2020";

/// An accumulation scheme for a NARK for R1CS.
/// This implementation is specialized for [`r1cs_nark`].
/// The construction is described in detail in Section 9 of [BCLMS20][bclms20].
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 10.1 in [BCLMS20][bclms20] for more details.
///
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
pub struct ASForR1CSNark<G, CS>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
{
    _affine: PhantomData<G>,
    _constraint_synthesizer: PhantomData<CS>,
}

impl<G, CS> ASForR1CSNark<G, CS>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
{
    fn check_input_instance_structure(
        input_instance: &InputInstance<G>,
        r1cs_input_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS input must be equal to those of the other R1CS inputs being
        // accumulated.
        if input_instance.r1cs_input.len() != r1cs_input_len {
            return Err(BoxedError::new(MalformedInput(
                "All R1CS inputs must be of equal length.".to_string(),
            )));
        }

        Ok(())
    }

    fn check_input_witness_structure(
        input_witness: &InputWitness<G::ScalarField>,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS witness must be equal to those of the other R1CS witnesses being
        // accumulated.
        if input_witness.second_round_message.blinded_witness.len() != r1cs_witness_len {
            return Err(BoxedError::new(MalformedInput(
                "All R1CS witnesses must be of equal length.".to_string(),
            )));
        }

        Ok(())
    }

    fn check_input_structure(
        input: &InputRef<'_, ConstraintF<G>, Self>,
        r1cs_input_len: usize,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        Self::check_input_instance_structure(input.instance, r1cs_input_len)?;
        Self::check_input_witness_structure(input.witness, r1cs_witness_len)?;

        // The randomness requirements of the first round message and the second round messages
        // must match.
        if input.instance.first_round_message.randomness.is_some()
            != input.witness.second_round_message.randomness.is_some()
        {
            return Err(BoxedError::new(MalformedInput(
                "The existence of the first round message randomness and the second round \
                    message randomness must be equal."
                    .to_string(),
            )));
        }

        Ok(())
    }

    fn check_accumulator_instance_structure(
        accumulator_instance: &AccumulatorInstance<G>,
        r1cs_input_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS input must be equal to those of the other R1CS inputs being
        // accumulated.
        if accumulator_instance.r1cs_input.len() != r1cs_input_len {
            return Err(BoxedError::new(MalformedAccumulator(
                "All R1CS inputs must be of equal length.".to_string(),
            )));
        }

        Ok(())
    }

    fn check_accumulator_witness_structure(
        accumulator_witness: &AccumulatorWitness<G::ScalarField>,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS witness must be equal to those of the other R1CS witnesses being
        // accumulated.
        if accumulator_witness.r1cs_blinded_witness.len() != r1cs_witness_len {
            return Err(BoxedError::new(MalformedAccumulator(
                "All R1CS witnesses must be of equal length.".to_string(),
            )));
        }

        Ok(())
    }

    fn check_r1cs_lengths(
        index_info: &IndexInfo,
        r1cs_input_len: usize,
        r1cs_witness_len: usize,
    ) -> bool {
        // The lengths of the R1CS inputs and witnesses to be accumulated must be supported by the
        // index key.
        return index_info.num_variables == r1cs_input_len + r1cs_witness_len;
    }

    fn compute_blinded_commitments(
        index_info: &IndexInfo,
        input_instances: &Vec<&InputInstance<G>>,
        nark_sponge: impl CryptographicSponge<ConstraintF<G>>,
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

            if let Some(first_msg_randomness) = instance.first_round_message.randomness.as_ref() {
                let gamma_challenge = R1CSNark::<G>::compute_challenge(
                    index_info,
                    instance.r1cs_input.as_slice(),
                    first_round_message,
                    nark_sponge.clone(),
                );

                let comm_a_proj =
                    comm_a.into_projective() + &first_msg_randomness.comm_r_a.mul(gamma_challenge);

                let comm_b_proj =
                    comm_b.into_projective() + &first_msg_randomness.comm_r_b.mul(gamma_challenge);

                let comm_c_proj =
                    comm_c.into_projective() + &first_msg_randomness.comm_r_c.mul(gamma_challenge);

                let comm_prod_proj = comm_prod.into_projective()
                    + &first_msg_randomness.comm_1.mul(gamma_challenge)
                    + &first_msg_randomness
                        .comm_2
                        .mul(gamma_challenge * &gamma_challenge);

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
        inputs: &Vec<InputRef<'_, ConstraintF<G>, Self>>,
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

                let randomness =
                    if let Some(second_msg_randomness) = second_round_message.randomness.as_ref() {
                        let rand_1 = second_msg_randomness.sigma_a;
                        let rand_2 = second_msg_randomness.sigma_b;
                        let rand_3 = second_msg_randomness.sigma_o;

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
        );

        let comm_r_b = PedersenCommitment::commit(
            &prover_key.nark_pk.ck,
            (matrix_vec_mul(b, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_2),
        );

        let comm_r_c = PedersenCommitment::commit(
            &prover_key.nark_pk.ck,
            (matrix_vec_mul(c, r1cs_r_input.as_slice(), r1cs_r_witness.as_slice())).as_slice(),
            Some(rand_3),
        );

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
        mut as_sponge: impl CryptographicSponge<ConstraintF<G>>,
    ) -> Vec<G::ScalarField> {
        absorb!(
            &mut as_sponge,
            as_matrices_hash.as_ref(),
            accumulator_instances,
            input_instances,
            proof_randomness
        );

        let mut squeeze = as_sponge.squeeze_nonnative_field_elements_with_sizes(
            vec![FieldElementSize::Truncated(128); num_challenges - 1].as_slice(),
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
            ASForHadamardProducts::<G>::combine_vectors(r1cs_inputs, beta_challenges, None);

        let combined_comm_a_proj =
            ASForHadamardProducts::<G>::combine_commitments(all_comm_a, beta_challenges, None);

        let combined_comm_b_proj =
            ASForHadamardProducts::<G>::combine_commitments(all_comm_b, beta_challenges, None);

        let combined_comm_c_proj =
            ASForHadamardProducts::<G>::combine_commitments(all_comm_c, beta_challenges, None);

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
            .chain(input_witnesses.iter().map(|witness| {
                witness
                    .second_round_message
                    .randomness
                    .as_ref()
                    .map(|r| &r.sigma_a)
            }));

        let all_sigma_b = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_b))
            .chain(input_witnesses.iter().map(|witness| {
                witness
                    .second_round_message
                    .randomness
                    .as_ref()
                    .map(|r| &r.sigma_b)
            }));

        let all_sigma_c = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_c))
            .chain(input_witnesses.iter().map(|witness| {
                witness
                    .second_round_message
                    .randomness
                    .as_ref()
                    .map(|r| &r.sigma_c)
            }));

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

        let combined_r1cs_blinded_witness = ASForHadamardProducts::<G>::combine_vectors(
            r1cs_blinded_witnesses,
            beta_challenges,
            None,
        );

        let witness_randomness = if prover_witness_randomness.is_some() {
            let combined_sigma_a =
                ASForHadamardProducts::<G>::combine_randomness(all_sigma_a, beta_challenges, None);

            let combined_sigma_b =
                ASForHadamardProducts::<G>::combine_randomness(all_sigma_b, beta_challenges, None);

            let combined_sigma_c =
                ASForHadamardProducts::<G>::combine_randomness(all_sigma_c, beta_challenges, None);

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

impl<G, CS> AccumulationScheme<ConstraintF<G>> for ASForR1CSNark<G, CS>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
{
    type PublicParameters =
        <ASForHadamardProducts<G> as AccumulationScheme<ConstraintF<G>>>::PublicParameters;

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

    fn setup(rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error> {
        <ASForHadamardProducts<G> as AccumulationScheme<ConstraintF<G>>>::setup(rng)
    }

    fn index(
        _public_params: &Self::PublicParameters,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ipk, ivk) = R1CSNark::<G>::index(&predicate_params, predicate_index.clone())
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

    fn prove<'a, S: CryptographicSponge<ConstraintF<G>>>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<ConstraintF<G>, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let nark_sponge = sponge.fork(r1cs_nark::PROTOCOL_NAME);
        let as_sponge = sponge.fork(PROTOCOL_NAME);
        let hp_sponge = sponge.fork(HP_AS_PROTOCOL_NAME);

        // Collect all of the inputs and accumulators into vectors and extract additional information from them.
        let mut inputs_zk_config = false;

        let mut r1cs_input_len: usize = 0;
        let mut r1cs_witness_len: usize = 0;
        let mut r1cs_len_set = false;

        let mut accumulator_instances = Vec::new();
        let mut accumulator_witnesses = Vec::new();
        for acc in old_accumulators {
            let instance = acc.instance;
            let witness = acc.witness;

            if !r1cs_len_set {
                r1cs_input_len = instance.r1cs_input.len();
                r1cs_witness_len = witness.r1cs_blinded_witness.len();

                if !Self::check_r1cs_lengths(
                    &prover_key.nark_pk.index_info,
                    r1cs_input_len,
                    r1cs_witness_len,
                ) {
                    return Err(BoxedError::new(MalformedAccumulator(
                        "The number of variables exceeds that supported by the prover key."
                            .to_string(),
                    )));
                }

                r1cs_len_set = true;
            }

            Self::check_accumulator_instance_structure(instance, r1cs_input_len)?;
            Self::check_accumulator_witness_structure(witness, r1cs_witness_len)?;

            inputs_zk_config = inputs_zk_config || witness.randomness.is_some();
            accumulator_instances.push(instance);
            accumulator_witnesses.push(witness);
        }

        let mut all_inputs = Vec::new();
        let mut input_instances = Vec::new();
        let mut input_witnesses = Vec::new();
        for input in inputs {
            let instance = input.instance;
            let witness = input.witness;

            if !r1cs_len_set {
                r1cs_input_len = instance.r1cs_input.len();
                r1cs_witness_len = witness.second_round_message.blinded_witness.len();

                if !Self::check_r1cs_lengths(
                    &prover_key.nark_pk.index_info,
                    r1cs_input_len,
                    r1cs_witness_len,
                ) {
                    return Err(BoxedError::new(MalformedInput(
                        "The number of variables exceeds that supported by the prover key."
                            .to_string(),
                    )));
                }

                r1cs_len_set = true;
            }

            Self::check_input_structure(&input, r1cs_input_len, r1cs_witness_len)?;

            inputs_zk_config =
                inputs_zk_config || instance.first_round_message.randomness.is_some();
            input_instances.push(instance);
            input_witnesses.push(witness);
            all_inputs.push(input);
        }

        if input_instances.len() + accumulator_instances.len() == 0 {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate.".to_string(),
            )));
        }

        let (make_zk_enabled, mut rng) = make_zk.into_components();
        if !make_zk_enabled && inputs_zk_config {
            return Err(BoxedError::new(ASError::MissingRng(
                "Accumulating inputs with hiding requires rng.".to_string(),
            )));
        }

        let (proof_randomness, prover_witness_randomness) = if make_zk_enabled {
            assert!(rng.is_some());
            let rng_moved = rng.unwrap();

            let index_info = &prover_key.nark_pk.index_info;
            let (proof_randomness, prover_witness_randomness) = Self::compute_prover_randomness(
                prover_key,
                rng_moved,
                index_info.num_instance_variables,
                index_info.num_variables - index_info.num_instance_variables,
            )?;

            rng = Some(rng_moved);
            (Some(proof_randomness), Some(prover_witness_randomness))
        } else {
            (None, None)
        };

        let num_addends = input_instances.len()
            + accumulator_instances.len()
            + if make_zk_enabled { 1 } else { 0 };

        // Run HP AS
        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                &prover_key.nark_pk.index_info,
                &input_instances,
                nark_sponge,
            );

        let combined_hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        let combined_hp_input_witnesses = Self::compute_hp_input_witnesses(prover_key, &all_inputs);

        let combined_hp_inputs_iter = combined_hp_input_instances
            .iter()
            .zip(&combined_hp_input_witnesses)
            .map(
                |(instance, witness)| InputRef::<_, ASForHadamardProducts<G>> { instance, witness },
            );

        let hp_accumulators_iter = accumulator_instances
            .iter()
            .zip(&accumulator_witnesses)
            .map(
                |(instance, witness)| AccumulatorRef::<_, ASForHadamardProducts<G>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            );

        let (hp_accumulator, hp_proof) = ASForHadamardProducts::<G>::prove(
            &prover_key.nark_pk.ck,
            combined_hp_inputs_iter,
            hp_accumulators_iter,
            if make_zk_enabled {
                assert!(rng.is_some());
                MakeZK::Enabled(rng.unwrap())
            } else {
                MakeZK::Disabled
            },
            Some(hp_sponge),
        )?;

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &prover_key.as_matrices_hash,
            &accumulator_instances,
            &input_instances,
            &proof_randomness,
            as_sponge,
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

        let accumulator = Accumulator::<_, Self> {
            instance: combined_acc_instance,
            witness: combined_acc_witness,
        };

        let proof = Proof {
            hp_proof,
            randomness: proof_randomness,
        };

        Ok((accumulator, proof))
    }

    fn verify<'a, S: CryptographicSponge<ConstraintF<G>>>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let nark_sponge = sponge.fork(r1cs_nark::PROTOCOL_NAME);
        let as_sponge = sponge.fork(PROTOCOL_NAME);
        let hp_sponge = sponge.fork(HP_AS_PROTOCOL_NAME);

        let input_instances = input_instances.into_iter().collect::<Vec<_>>();
        let old_accumulator_instances = old_accumulator_instances.into_iter().collect::<Vec<_>>();

        if input_instances.len() + old_accumulator_instances.len() == 0 {
            return Ok(false);
        }

        let r1cs_input_len = if old_accumulator_instances.is_empty() {
            input_instances[0].r1cs_input.len()
        } else {
            old_accumulator_instances[0].r1cs_input.len()
        };

        for instance in &input_instances {
            if Self::check_input_instance_structure(instance, r1cs_input_len).is_err() {
                return Ok(false);
            }
        }

        for instance in &old_accumulator_instances {
            if Self::check_accumulator_instance_structure(instance, r1cs_input_len).is_err() {
                return Ok(false);
            }
        }

        let num_addends = input_instances.len()
            + old_accumulator_instances.len()
            + if proof.randomness.is_some() { 1 } else { 0 };

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &verifier_key.as_matrices_hash,
            &old_accumulator_instances,
            &input_instances,
            &proof.randomness,
            as_sponge,
        );

        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                &verifier_key.nark_index,
                &input_instances,
                nark_sponge,
            );

        let hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        let hp_accumulator_instances = old_accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        let hp_verify = ASForHadamardProducts::<G>::verify(
            &verifier_key.nark_index.num_constraints,
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
            Some(hp_sponge),
        )?;

        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &old_accumulator_instances,
            &beta_challenges,
            proof.randomness.as_ref(),
        );

        Ok(hp_verify
            && r1cs_input.eq(&new_accumulator_instance.r1cs_input)
            && comm_a.eq(&new_accumulator_instance.comm_a)
            && comm_b.eq(&new_accumulator_instance.comm_b)
            && comm_c.eq(&new_accumulator_instance.comm_c))
    }

    fn decide<'a, S: CryptographicSponge<ConstraintF<G>>>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, Self>,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let hp_sponge = sponge.fork(HP_AS_PROTOCOL_NAME);

        let instance = accumulator.instance;
        let witness = accumulator.witness;

        if !Self::check_r1cs_lengths(
            &decider_key.index_info,
            instance.r1cs_input.len(),
            witness.r1cs_blinded_witness.len(),
        ) {
            return Ok(false);
        }

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
        );

        let comm_b = PedersenCommitment::commit(
            &decider_key.ck,
            b_times_blinded_witness.as_slice(),
            sigma_b,
        );

        let comm_c = PedersenCommitment::commit(
            &decider_key.ck,
            c_times_blinded_witness.as_slice(),
            sigma_c,
        );

        let comm_check = comm_a.eq(&instance.comm_a)
            && comm_b.eq(&instance.comm_b)
            && comm_c.eq(&instance.comm_c);

        Ok(comm_check
            && ASForHadamardProducts::<G>::decide(
                &decider_key.ck,
                AccumulatorRef::<_, ASForHadamardProducts<G>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
                Some(hp_sponge),
            )?)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::r1cs_nark_as::data_structures::{InputInstance, InputWitness};
    use crate::r1cs_nark_as::r1cs_nark::IndexProverKey;
    use crate::r1cs_nark_as::r1cs_nark::R1CSNark;
    use crate::r1cs_nark_as::{r1cs_nark, ASForR1CSNark};
    use crate::tests::*;
    use crate::AccumulationScheme;
    use crate::ConstraintF;
    use ark_ec::AffineCurve;
    use ark_ff::PrimeField;
    use ark_relations::lc;
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
        SynthesisError,
    };
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use ark_std::marker::PhantomData;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;
    use rand_core::RngCore;

    #[derive(Clone)]
    // num_variables = num_inputs + 2
    pub struct ASForR1CSNarkTestParams {
        // At least one input required.
        pub num_inputs: usize,

        // At least one constraint required.
        pub num_constraints: usize,

        pub make_zk: bool,
    }

    impl TestParameters for ASForR1CSNarkTestParams {
        fn make_zk(&self) -> bool {
            self.make_zk
        }
    }

    #[derive(Clone)]
    pub(crate) struct DummyCircuit<F: PrimeField> {
        pub a: Option<F>,
        pub b: Option<F>,
        pub params: ASForR1CSNarkTestParams,
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

    pub struct ASForR1CSNarkTestInput<CF: PrimeField, S: CryptographicSponge<CF>> {
        _cf: PhantomData<CF>,
        _sponge: PhantomData<S>,
    }

    impl<G, S> ASTestInput<ConstraintF<G>, ASForR1CSNark<G, DummyCircuit<G::ScalarField>>>
        for ASForR1CSNarkTestInput<ConstraintF<G>, S>
    where
        G: AffineCurve + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = ASForR1CSNarkTestParams;
        type InputParams = (Self::TestParams, IndexProverKey<G>);

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <ASForR1CSNark<G, DummyCircuit<G::ScalarField>> as AccumulationScheme<
                ConstraintF<G>,
            >>::PredicateParams,
            <ASForR1CSNark<G, DummyCircuit<G::ScalarField>> as AccumulationScheme<
                ConstraintF<G>,
            >>::PredicateIndex,
        ) {
            let nark_pp = R1CSNark::<G>::setup();
            let circuit = DummyCircuit {
                a: Some(G::ScalarField::rand(rng)),
                b: Some(G::ScalarField::rand(rng)),
                params: test_params.clone(),
            };

            let (pk, _) = R1CSNark::<G>::index(&nark_pp, circuit.clone()).unwrap();

            ((test_params.clone(), pk), nark_pp, circuit)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<ConstraintF<G>, ASForR1CSNark<G, DummyCircuit<G::ScalarField>>>> {
            let (test_params, ipk) = input_params;

            let mut inputs = Vec::with_capacity(num_inputs);
            for _ in 0..num_inputs {
                let circuit = DummyCircuit {
                    a: Some(G::ScalarField::rand(rng)),
                    b: Some(G::ScalarField::rand(rng)),
                    params: input_params.0.clone(),
                };

                let nark_sponge = S::new().fork(r1cs_nark::PROTOCOL_NAME);

                let proof = R1CSNark::<G>::prove(
                    ipk,
                    circuit.clone(),
                    test_params.make_zk,
                    Some(nark_sponge),
                    Some(rng),
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
                };

                let witness = InputWitness {
                    second_round_message: proof.second_msg,
                };

                inputs.push(Input::<_, ASForR1CSNark<G, DummyCircuit<G::ScalarField>>> {
                    instance,
                    witness,
                });
            }

            inputs
        }
    }

    type G = ark_pallas::Affine;
    type F = ark_pallas::Fr;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = ASForR1CSNark<G, DummyCircuit<F>>;
    type I = ASForR1CSNarkTestInput<CF, Sponge>;

    type Tests = ASTests<CF, AS, I, Sponge>;

    #[test]
    pub fn single_input_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_no_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: false,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&ASForR1CSNarkTestParams {
            num_inputs: 5,
            num_constraints: 10,
            make_zk: true,
        })
    }
}
