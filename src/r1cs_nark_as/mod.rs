use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::ASError::{MalformedAccumulator, MalformedInput};
use crate::error::{ASError, BoxedError};
use crate::hp_as::ASForHadamardProducts;
use crate::hp_as::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
    InputWitnessRandomness as HPInputWitnessRandomness,
};
use crate::r1cs_nark_as::r1cs_nark::{
    hash_matrices, matrix_vec_mul, FirstRoundMessage, IndexProverKey, IndexVerifierKey, R1CSNark,
    SecondRoundMessage,
};
use crate::ConstraintF;
use crate::{AccumulationScheme, MakeZK};

use crate::trivial_pc::PedersenCommitment;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::One;
use ark_ff::UniformRand;
use ark_sponge::{absorb, Absorb, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::rand::RngCore;
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;

mod data_structures;
pub use data_structures::*;

/// A simple non-interactive argument of knowledge for R1CS.
pub mod r1cs_nark;

/// The verifier constraints of [`ASForR1CSNark`].
#[cfg(feature = "r1cs")]
pub mod constraints;

pub(crate) const HP_AS_PROTOCOL_NAME: &[u8] = b"AS-FOR-HP-2020";
pub(crate) const PROTOCOL_NAME: &[u8] = b"AS-FOR-R1CS-NARK-2020";

/// Size of squeezed challenges in terms of number of bits.
pub(self) const CHALLENGE_SIZE: usize = 128;

/// An accumulation scheme for a NARK for R1CS, specialized for [`r1cs_nark`].
/// The construction is described in detail in Section 8 of [\[BCLMS20\]][bclms20].
///
/// The implementation differs from the construction in the paper in that the full R1CS input is
/// included in the accumulator instance, rather than its commitment. The construction in the paper
/// commits to the R1CS input to bound the public input size for the paper's PCD construction.
/// However, the PCD implementation will hash the inputs, so the committing to the R1CS input for
/// the accumulator instance is no longer necessary.
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 9.1 in [\[BCLMS20\]][bclms20] for more details.
///
/// [bclms20]: https://eprint.iacr.org/2020/1618
///
/// # Example Input
/// ```
///
/// use ark_accumulation::r1cs_nark_as::{ASForR1CSNark, InputInstance};
/// use ark_accumulation::r1cs_nark_as::r1cs_nark::{FirstRoundMessage, SecondRoundMessage};
/// use ark_accumulation::Input;
/// use ark_ec::AffineCurve;
/// use ark_ff::Field;
/// use ark_relations::r1cs::ConstraintSynthesizer;
/// use ark_sponge::{Absorbable, CryptographicSponge};
///
/// type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
///
/// // An accumulation input for this scheme is formed from:
/// // 1. The R1CS input for an indexed relation:                          `input`
/// // 2. The NARK prover's first round message for the indexed relation:  `first_msg`
/// // 3. The NARK prover's second round message for the indexed relation: `second_msg`
/// fn new_accumulation_input<G, S>(
///     input: Vec<G::ScalarField>,
///     first_msg: FirstRoundMessage<G>,
///     second_msg: SecondRoundMessage<G::ScalarField>,
/// ) -> Input<ConstraintF<G>, S, ASForR1CSNark<G, S>>
///     where
///         G: AffineCurve + Absorb,
///         ConstraintF<G>: Absorb,
///         S: CryptographicSponge
/// {
///     let instance = InputInstance {
///         r1cs_input: input,
///         first_round_message: first_msg,
///     };
///
///     let witness = second_msg;
///
///     Input::<_, _, ASForR1CSNark<G, S>> { instance, witness }
/// }
/// ```
pub struct ASForR1CSNark<G, S>
where
    G: AffineCurve + Absorb,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> ASForR1CSNark<G, S>
where
    G: AffineCurve + Absorb,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
{
    /// Returns a new sponge from a base sponge that is used by the NARK.
    pub fn nark_sponge(base_sponge: &S) -> S {
        base_sponge.fork(r1cs_nark::PROTOCOL_NAME)
    }

    /// Returns a new sponge from a base sponge that is used by this accumulation scheme.
    fn as_sponge(base_sponge: &S) -> S {
        base_sponge.fork(PROTOCOL_NAME)
    }

    /// Returns a new sponge from a base sponge that is used by the accumulation scheme for
    /// Hadamard products.
    fn hp_sponge(base_sponge: &S) -> S {
        base_sponge.fork(HP_AS_PROTOCOL_NAME)
    }

    /// Check that the input instance is properly structured.
    fn check_input_instance_structure(
        input_instance: &InputInstance<G>,
        r1cs_input_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS input must be equal to those of the other R1CS inputs being
        // accumulated.
        if input_instance.r1cs_input.len() != r1cs_input_len {
            return Err(BoxedError::new(MalformedInput(
                "All R1CS input lengths must be equal and supported by the index prover key."
                    .to_string(),
            )));
        }

        Ok(())
    }

    /// Check that the input witness is properly structured.
    fn check_input_witness_structure(
        input_witness: &InputWitness<G::ScalarField>,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS witness must be equal to those of the other R1CS witnesses being
        // accumulated.
        if input_witness.blinded_witness.len() != r1cs_witness_len {
            return Err(BoxedError::new(MalformedInput(
                "All R1CS witness lengths must be equal and supported by the index prover key."
                    .to_string(),
            )));
        }

        Ok(())
    }

    /// Check that the input is properly structured.
    fn check_input_structure(
        input: &InputRef<'_, ConstraintF<G>, S, Self>,
        r1cs_input_len: usize,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        Self::check_input_instance_structure(input.instance, r1cs_input_len)?;
        Self::check_input_witness_structure(input.witness, r1cs_witness_len)?;

        // The randomness requirements of the first round message and the second round messages
        // must match.
        if input.instance.first_round_message.randomness.is_some()
            != input.witness.randomness.is_some()
        {
            return Err(BoxedError::new(MalformedInput(
                "The existence of the first round message randomness and the second round \
                    message randomness must be equal."
                    .to_string(),
            )));
        }

        Ok(())
    }

    /// Check that the accumulator instance is properly structured.
    fn check_accumulator_instance_structure(
        accumulator_instance: &AccumulatorInstance<G>,
        r1cs_input_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS input must be equal to those of the other R1CS inputs being
        // accumulated.
        if accumulator_instance.r1cs_input.len() != r1cs_input_len {
            return Err(BoxedError::new(MalformedAccumulator(
                "All R1CS input lengths must be equal and supported by the index prover key."
                    .to_string(),
            )));
        }

        Ok(())
    }

    /// Check that the accumulator witness is properly structured.
    fn check_accumulator_witness_structure(
        accumulator_witness: &AccumulatorWitness<G::ScalarField>,
        r1cs_witness_len: usize,
    ) -> Result<(), BoxedError> {
        // The length of the R1CS witness must be equal to those of the other R1CS witnesses being
        // accumulated.
        if accumulator_witness.r1cs_blinded_witness.len() != r1cs_witness_len {
            return Err(BoxedError::new(MalformedAccumulator(
                "All R1CS witness lengths must be equal and supported by the index prover key."
                    .to_string(),
            )));
        }

        Ok(())
    }

    /// Blinds the commitments from the first round messages.
    fn compute_blinded_commitments(
        nark_matrices_hash: &[u8; 32],
        input_instances: &Vec<&InputInstance<G>>,
        nark_sponge: S,
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
                let gamma_challenge = R1CSNark::<G, S>::compute_challenge(
                    nark_matrices_hash,
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

    /// Compute the input instances for HP_AS using the blinded commitments.
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

    /// Compute the input witnesses for HP_AS using the accumulation inputs.
    fn compute_hp_input_witnesses<'a>(
        prover_key: &ProverKey<G>,
        input_instances: &Vec<&InputInstance<G>>,
        input_witnesses: &Vec<&InputWitness<G::ScalarField>>,
    ) -> Vec<HPInputWitness<G::ScalarField>> {
        assert_eq!(input_instances.len(), input_witnesses.len());

        input_instances
            .into_iter()
            .zip(input_witnesses)
            .map(|(instance, witness)| {
                let second_round_message: &SecondRoundMessage<G::ScalarField> = witness;

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

    /// Generate the randomness used by the accumulation prover.
    fn generate_prover_randomness(
        prover_key: &ProverKey<G>,
        r1cs_input_len: usize,
        r1cs_witness_len: usize,
        rng: &mut dyn RngCore,
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

    /// Computes the beta challenges using the provided sponge.
    fn compute_beta_challenges(
        num_challenges: usize,
        as_matrices_hash: &[u8; 32],
        accumulator_instances: &Vec<&AccumulatorInstance<G>>,
        input_instances: &Vec<&InputInstance<G>>,
        proof_randomness: &Option<ProofRandomness<G>>,
        mut as_sponge: impl CryptographicSponge,
    ) -> Vec<G::ScalarField> {
        absorb!(
            &mut as_sponge,
            as_matrices_hash.as_ref(),
            accumulator_instances,
            input_instances,
            proof_randomness
        );

        let mut squeeze = as_sponge.squeeze_field_elements_with_sizes::<G::ScalarField>(
            vec![FieldElementSize::Truncated(CHALLENGE_SIZE); num_challenges - 1].as_slice(),
        );

        let mut outputs = Vec::with_capacity(num_challenges);
        outputs.push(G::ScalarField::one());
        outputs.append(&mut squeeze);

        outputs
    }

    /// Computes a part of a new accumulator instance. Does not compute the HP_AS input instance, so
    /// an accumulator instance is not yet fully constructed.
    fn compute_accumulator_instance_components(
        input_instances: &Vec<&InputInstance<G>>,
        all_blinded_comm_a: &Vec<G>,
        all_blinded_comm_b: &Vec<G>,
        all_blinded_comm_c: &Vec<G>,
        accumulator_instances: &Vec<&AccumulatorInstance<G>>,
        beta_challenges: &Vec<G::ScalarField>,
        proof_randomness: Option<&ProofRandomness<G>>,
    ) -> (
        Vec<G::ScalarField>, // Combined R1CS input
        G,                   // Combined comm_a
        G,                   // Combined comm_b
        G,                   // Combined comm_c
    ) {
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
            ASForHadamardProducts::<G, S>::combine_vectors(r1cs_inputs, beta_challenges, None);

        let combined_comm_a_proj =
            ASForHadamardProducts::<G, S>::combine_commitments(all_comm_a, beta_challenges, None);

        let combined_comm_b_proj =
            ASForHadamardProducts::<G, S>::combine_commitments(all_comm_b, beta_challenges, None);

        let combined_comm_c_proj =
            ASForHadamardProducts::<G, S>::combine_commitments(all_comm_c, beta_challenges, None);

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

    /// Computes a part of a new accumulator witness. Does not compute the HP_AS input witness, so
    /// an accumulator witness is not yet fully constructed.
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
                    .map(|witness| &witness.blinded_witness),
            );

        let all_sigma_a = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_a))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_a)),
            );

        let all_sigma_b = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_b))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_b)),
            );

        let all_sigma_c = accumulator_witnesses
            .iter()
            .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_c))
            .chain(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.sigma_c)),
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

        let combined_r1cs_blinded_witness = ASForHadamardProducts::<G, S>::combine_vectors(
            r1cs_blinded_witnesses,
            beta_challenges,
            None,
        );

        let witness_randomness = if prover_witness_randomness.is_some() {
            let combined_sigma_a = ASForHadamardProducts::<G, S>::combine_randomness(
                all_sigma_a,
                beta_challenges,
                None,
            );

            let combined_sigma_b = ASForHadamardProducts::<G, S>::combine_randomness(
                all_sigma_b,
                beta_challenges,
                None,
            );

            let combined_sigma_c = ASForHadamardProducts::<G, S>::combine_randomness(
                all_sigma_c,
                beta_challenges,
                None,
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

impl<G, S> AccumulationScheme<ConstraintF<G>, S> for ASForR1CSNark<G, S>
where
    G: AffineCurve + Absorb,
    ConstraintF<G>: Absorb,
    S: CryptographicSponge,
{
    type PublicParameters =
        <ASForHadamardProducts<G, S> as AccumulationScheme<ConstraintF<G>, S>>::PublicParameters;

    type PredicateParams = ();
    type PredicateIndex = (IndexProverKey<G>, IndexVerifierKey<G>);

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
        <ASForHadamardProducts<G, S> as AccumulationScheme<ConstraintF<G>, S>>::setup(rng)
    }

    fn index(
        _public_params: &Self::PublicParameters,
        _predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let (ipk, ivk) = predicate_index;

        let as_matrices_hash = hash_matrices(PROTOCOL_NAME, &ipk.a, &ipk.b, &ipk.c);

        let pk = ProverKey {
            nark_pk: ipk.clone(),
            as_matrices_hash: as_matrices_hash.clone(),
        };

        let vk = VerifierKey {
            num_instance_variables: ivk.index_info.num_instance_variables,
            num_constraints: ivk.index_info.num_constraints,
            nark_matrices_hash: ivk.index_info.matrices_hash.clone(),
            as_matrices_hash,
        };

        let dk = ivk.clone();

        Ok((pk, vk, dk))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, S, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, S, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<ConstraintF<G>, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        assert!(!sponge.is_none());
        let sponge = sponge.unwrap();
        let nark_sponge = Self::nark_sponge(&sponge);
        let as_sponge = Self::as_sponge(&sponge);
        let hp_sponge = Self::hp_sponge(&sponge);

        let r1cs_input_len: usize = prover_key.nark_pk.index_info.num_instance_variables;
        let r1cs_witness_len: usize = prover_key.nark_pk.index_info.num_variables - r1cs_input_len;

        // Collect the accumulator instances and witnesses. Run checks on them.
        let mut old_accumulator_instances = Vec::new();
        let mut old_accumulator_witnesses = Vec::new();
        for acc in old_accumulators {
            let instance = acc.instance;
            let witness = acc.witness;

            Self::check_accumulator_instance_structure(instance, r1cs_input_len)?;
            Self::check_accumulator_witness_structure(witness, r1cs_witness_len)?;

            old_accumulator_instances.push(instance);
            old_accumulator_witnesses.push(witness);
        }

        // Collect the accumulator instances and witnesses. Run checks on them.
        let mut input_instances = Vec::new();
        let mut input_witnesses = Vec::new();
        for input in inputs {
            let instance = input.instance;
            let witness = input.witness;

            Self::check_input_structure(&input, r1cs_input_len, r1cs_witness_len)?;

            input_instances.push(instance);
            input_witnesses.push(witness);
        }

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        let default_input_witness;
        if input_instances.is_empty() && old_accumulator_instances.is_empty() {
            default_input_instance = Some(InputInstance::zero(r1cs_input_len, false));
            default_input_witness = Some(InputWitness::zero(r1cs_witness_len, false));

            input_instances.push(default_input_instance.as_ref().unwrap());
            input_witnesses.push(default_input_witness.as_ref().unwrap());
        }

        let (make_zk_enabled, mut rng) = make_zk.into_components();
        // Ensure that none of the inputs or accumulators require zero-knowledge.
        if !make_zk_enabled {
            for witness in &input_witnesses {
                if witness.randomness.is_some() {
                    return Err(BoxedError::new(ASError::MissingRng(
                        "Accumulating inputs with hiding requires rng.".to_string(),
                    )));
                }
            }

            for witness in &old_accumulator_witnesses {
                if witness.randomness.is_some() {
                    return Err(BoxedError::new(ASError::MissingRng(
                        "Accumulating accumulators with hiding requires rng.".to_string(),
                    )));
                }
            }
        }

        // Step 4 of the scheme's accumulation prover, as detailed in BCLMS20.
        // We perform Step 4 here because the optional rng will be consumed later in the method, so
        // we use it here first.
        let (proof_randomness, prover_witness_randomness) = if make_zk_enabled {
            // If make_zk, then rng should exist here.
            assert!(rng.is_some());

            let rng_moved = rng.unwrap();

            let index_info = &prover_key.nark_pk.index_info;
            let (proof_randomness, prover_witness_randomness) = Self::generate_prover_randomness(
                prover_key,
                index_info.num_instance_variables,
                index_info.num_variables - index_info.num_instance_variables,
                rng_moved,
            )?;

            rng = Some(rng_moved);
            (Some(proof_randomness), Some(prover_witness_randomness))
        } else {
            (None, None)
        };

        // Step 1 of the scheme's accumulation prover, as detailed in BCLMS20.
        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                &prover_key.nark_pk.index_info.matrices_hash,
                &input_instances,
                nark_sponge,
            );

        // Step 2 of the scheme's accumulation prover, as detailed in BCLMS20.
        let combined_hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        let combined_hp_input_witnesses =
            Self::compute_hp_input_witnesses(prover_key, &input_instances, &input_witnesses);

        // Step 3 of the scheme's accumulation prover, as detailed in BCLMS20.
        let combined_hp_inputs_iter = combined_hp_input_instances
            .iter()
            .zip(&combined_hp_input_witnesses)
            .map(
                |(instance, witness)| InputRef::<_, _, ASForHadamardProducts<G, S>> {
                    instance,
                    witness,
                },
            );

        let hp_accumulators_iter = old_accumulator_instances
            .iter()
            .zip(&old_accumulator_witnesses)
            .map(
                |(instance, witness)| AccumulatorRef::<_, _, ASForHadamardProducts<G, S>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            );

        let (hp_accumulator, hp_proof) = ASForHadamardProducts::<G, S>::prove(
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

        // Step 4 was previously executed above.

        // Step 5 of the scheme's accumulation prover, as detailed in BCLMS20.
        let num_addends = input_instances.len()
            + old_accumulator_instances.len()
            + if make_zk_enabled { 1 } else { 0 };

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &prover_key.as_matrices_hash,
            &old_accumulator_instances,
            &input_instances,
            &proof_randomness,
            as_sponge,
        );

        // Step 6 of the scheme's accumulation prover, as detailed in BCLMS20.
        let (r1cs_input, comm_a, comm_b, comm_c) = Self::compute_accumulator_instance_components(
            &input_instances,
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_c,
            &old_accumulator_instances,
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

        // Step 7 of the scheme's accumulation prover, as detailed in BCLMS20.
        let (r1cs_blinded_witness, randomness) = Self::compute_accumulator_witness_components(
            &input_witnesses,
            &old_accumulator_witnesses,
            &beta_challenges,
            prover_witness_randomness.as_ref(),
        );

        let combined_acc_witness = AccumulatorWitness {
            r1cs_blinded_witness,
            hp_witness: hp_accumulator.witness,
            randomness,
        };

        // Step 8 of the scheme's accumulation prover, as detailed in BCLMS20.
        let accumulator = Accumulator::<_, _, Self> {
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
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        assert!(!sponge.is_none());
        let sponge = sponge.unwrap();

        let nark_sponge = Self::nark_sponge(&sponge);
        let as_sponge = Self::as_sponge(&sponge);
        let hp_sponge = Self::hp_sponge(&sponge);

        let make_zk_enabled = proof.randomness.is_some();
        let r1cs_input_len = verifier_key.num_instance_variables;

        let mut input_instances = input_instances.into_iter().collect::<Vec<_>>();
        for instance in &input_instances {
            if Self::check_input_instance_structure(instance, r1cs_input_len).is_err() {
                return Ok(false);
            }
        }

        let old_accumulator_instances = old_accumulator_instances.into_iter().collect::<Vec<_>>();
        for instance in &old_accumulator_instances {
            if Self::check_accumulator_instance_structure(instance, r1cs_input_len).is_err() {
                return Ok(false);
            }
        }

        // Default input in the case there are no provided inputs or accumulators.
        let default_input_instance;
        if input_instances.is_empty() && old_accumulator_instances.is_empty() {
            default_input_instance = Some(InputInstance::zero(r1cs_input_len, false));
            input_instances.push(default_input_instance.as_ref().unwrap());
        }

        // Steps 1-2 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let (all_blinded_comm_a, all_blinded_comm_b, all_blinded_comm_c, all_blinded_comm_prod) =
            Self::compute_blinded_commitments(
                &verifier_key.nark_matrices_hash,
                &input_instances,
                nark_sponge,
            );

        // Step 3 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let hp_input_instances = Self::compute_hp_input_instances(
            &all_blinded_comm_a,
            &all_blinded_comm_b,
            &all_blinded_comm_prod,
        );

        // Step 4 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let hp_accumulator_instances = old_accumulator_instances
            .iter()
            .map(|instance| &instance.hp_instance);

        let hp_verify = ASForHadamardProducts::<G, S>::verify(
            &verifier_key.num_constraints,
            &hp_input_instances,
            hp_accumulator_instances,
            &new_accumulator_instance.hp_instance,
            &proof.hp_proof,
            Some(hp_sponge),
        )?;

        // Step 5 of the scheme's accumulation verifier, as detailed in BCLMS20.
        let num_addends = input_instances.len()
            + old_accumulator_instances.len()
            + if make_zk_enabled { 1 } else { 0 };

        let beta_challenges = Self::compute_beta_challenges(
            num_addends,
            &verifier_key.as_matrices_hash,
            &old_accumulator_instances,
            &input_instances,
            &proof.randomness,
            as_sponge,
        );

        // Step 6 of the scheme's accumulation verifier, as detailed in BCLMS20.
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

    fn decide<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, S, Self>,
        _sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let instance = accumulator.instance;
        let witness = accumulator.witness;

        let r1cs_input_len: usize = decider_key.index_info.num_instance_variables;
        let r1cs_witness_len: usize = decider_key.index_info.num_variables - r1cs_input_len;

        if Self::check_accumulator_instance_structure(instance, r1cs_input_len).is_err()
            || Self::check_accumulator_witness_structure(witness, r1cs_witness_len).is_err()
        {
            return Ok(false);
        }

        // Step 3 of the scheme's accumulation decider, as detailed in BCLMS20.
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

        // Steps 4-7 of the scheme's accumulation decider, as detailed in BCLMS20.
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
            // Step 8 of the scheme's accumulation decider, as detailed in BCLMS20.
            && ASForHadamardProducts::<G, S>::decide( &decider_key.ck,
                AccumulatorRef::<_, _, ASForHadamardProducts<G, S>> {
                    instance: &instance.hp_instance,
                    witness: &witness.hp_witness,
                },
            None
            )?)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::r1cs_nark_as::data_structures::InputInstance;
    use crate::r1cs_nark_as::r1cs_nark::IndexProverKey;
    use crate::r1cs_nark_as::r1cs_nark::R1CSNark;
    use crate::r1cs_nark_as::ASForR1CSNark;
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
    use ark_sponge::{Absorb, CryptographicSponge};
    use ark_std::marker::PhantomData;
    use ark_std::rand::RngCore;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;

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

    pub struct ASForR1CSNarkTestInput<CF: PrimeField, S: CryptographicSponge> {
        _cf: PhantomData<CF>,
        _sponge: PhantomData<S>,
    }

    impl<G, S> ASTestInput<ConstraintF<G>, S, ASForR1CSNark<G, S>>
        for ASForR1CSNarkTestInput<ConstraintF<G>, S>
    where
        G: AffineCurve + Absorb,
        ConstraintF<G>: Absorb,
        S: CryptographicSponge,
    {
        type TestParams = ASForR1CSNarkTestParams;
        type InputParams = (Self::TestParams, IndexProverKey<G>);

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <ASForR1CSNark<G, S> as AccumulationScheme<ConstraintF<G>, S>>::PredicateParams,
            <ASForR1CSNark<G, S> as AccumulationScheme<ConstraintF<G>, S>>::PredicateIndex,
        ) {
            let nark_pp = R1CSNark::<G, S>::setup();
            let circuit = DummyCircuit {
                a: Some(G::ScalarField::rand(rng)),
                b: Some(G::ScalarField::rand(rng)),
                params: test_params.clone(),
            };

            let (ipk, ivk) = R1CSNark::<G, S>::index(&nark_pp, circuit.clone()).unwrap();

            (
                (test_params.clone(), ipk.clone()),
                nark_pp,
                (ipk, ivk.clone()),
            )
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
            sponge: S,
        ) -> Vec<Input<ConstraintF<G>, S, ASForR1CSNark<G, S>>> {
            let (test_params, ipk) = input_params;

            let mut inputs = Vec::with_capacity(num_inputs);
            for _ in 0..num_inputs {
                let circuit = DummyCircuit {
                    a: Some(G::ScalarField::rand(rng)),
                    b: Some(G::ScalarField::rand(rng)),
                    params: input_params.0.clone(),
                };

                let nark_sponge = ASForR1CSNark::<G, S>::nark_sponge(&sponge);

                let proof = R1CSNark::<G, S>::prove(
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

                let witness = proof.second_msg;

                inputs.push(Input::<_, _, ASForR1CSNark<G, S>> { instance, witness });
            }

            inputs
        }
    }

    type G = ark_pallas::Affine;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = ASForR1CSNark<G, Sponge>;
    type I = ASForR1CSNarkTestInput<CF, Sponge>;

    type Tests = ASTests<CF, Sponge, AS, I>;

    #[test]
    pub fn single_input_init_test_no_zk() -> Result<(), BoxedError> {
        Tests::single_input_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn single_input_init_test_zk() -> Result<(), BoxedError> {
        Tests::single_input_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_init_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_input_init_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn multiple_inputs_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_accumulation_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn no_inputs_init_test_no_zk() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: false,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }

    #[test]
    pub fn no_inputs_init_test_zk() -> Result<(), BoxedError> {
        Tests::no_inputs_init_test(
            &ASForR1CSNarkTestParams {
                num_inputs: 5,
                num_constraints: 10,
                make_zk: true,
            },
            &poseidon_parameters_for_test::<CF>(),
        )
    }
}
