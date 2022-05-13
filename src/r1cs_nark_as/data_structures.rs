use crate::hp_as::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness, ProductPolynomialCommitment,
    Proof as HPProof, ProofHidingCommitments,
};
use crate::r1cs_nark_as::r1cs_nark::{FirstRoundMessage, IndexProverKey, SecondRoundMessage};

use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField, Zero};
use ark_relations::r1cs::Matrix;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use ark_std::io::{Read, Write};
use ark_std::vec::Vec;

/// The [`PredicateIndex`][predicate_index] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [predicate_index]: crate::AccumulationScheme::PredicateIndex
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone)]
pub struct PredicateIndex<F: Field> {
    /// The `A` matrix for the R1CS instance.
    pub a: Matrix<F>,

    /// The `B` matrix for the R1CS instance.
    pub b: Matrix<F>,

    /// The `C` matrix for the R1CS instance.
    pub c: Matrix<F>,

    /// The index of the relation to be verified by the NARK.
    pub index: usize,
}

/// The [`ProverKey`][pk] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [pk]: crate::AccumulationScheme::ProverKey
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// The NARK prover key.
    pub nark_pk: IndexProverKey<G>,

    /// Hash of the matrices for the accumulation scheme.
    pub(crate) as_matrices_hash: [u8; 32],
}

/// The [`VerifierKey`][vk] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [vk]: crate::AccumulationScheme::VerifierKey
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone)]
pub struct VerifierKey {
    /// The number of public input (i.e. instance) variables.
    pub(crate) num_instance_variables: usize,

    /// The number of constraints.
    pub(crate) num_constraints: usize,

    /// Hash of the matrices for the NARK.
    pub(crate) nark_matrices_hash: [u8; 32],

    /// Hash of the matrices for the accumulation scheme.
    pub(crate) as_matrices_hash: [u8; 32],
}

impl VerifierKey {
    /// Outputs a placeholder for a verifier key to be used in PCD circuit setup.
    /// The constraints equivalent of the verifier key only requires the correct public input
    /// length while everything else may be left as unknown variables.
    pub fn placeholder(input_len: usize) -> Self {
        Self {
            num_instance_variables: input_len,
            num_constraints: 0,
            nark_matrices_hash: [0u8; 32],
            as_matrices_hash: [0u8; 32],
        }
    }
}

impl Absorb for VerifierKey {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            self.num_instance_variables,
            self.num_constraints,
            self.nark_matrices_hash.to_vec(),
            self.as_matrices_hash.to_vec()
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            self.num_instance_variables,
            self.num_constraints,
            self.nark_matrices_hash.to_vec(),
            self.as_matrices_hash.to_vec()
        );
        dest.extend(tmp);
    }
}

/// The [`InputInstance`][input_instance] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// An R1CS input for the indexed relation.
    pub r1cs_input: Vec<G::ScalarField>,

    /// The sigma protocol's prover commitment of the NARK.
    pub first_round_message: FirstRoundMessage<G>,
}

impl<G: AffineCurve> InputInstance<G> {
    /// Returns a default input instance.
    pub fn zero(input_len: usize, make_zk: bool) -> Self {
        Self {
            r1cs_input: vec![G::ScalarField::zero(); input_len],
            first_round_message: FirstRoundMessage::zero(make_zk),
        }
    }
}

impl<G: AffineCurve + Absorb> Absorb for InputInstance<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message
        );
        dest.extend(tmp);
    }
}

/// The [`InputWitness`][input_witness] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [input_witness]: crate::AccumulationScheme::InputWitness
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
pub type InputWitness<F> = SecondRoundMessage<F>;

/// The [`AccumulatorInstance`][acc_instance] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [acc_instance]: crate::AccumulationScheme::AccumulatorInstance
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorInstance<G: AffineCurve> {
    /// An input for the indexed relation.
    pub(crate) r1cs_input: Vec<G::ScalarField>,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: G,

    /// Pedersen commitment to the `Bz` vector.
    pub(crate) comm_b: G,

    /// Pedersen commitment to the `Cz` vector.
    pub(crate) comm_c: G,

    /// The Hadamard product accumulation scheme input instance.
    pub(crate) hp_instance: HPInputInstance<G>,
}

impl<G: AffineCurve> AccumulatorInstance<G> {
    /// Outputs a placeholder for an accumulator instance to be used in the PCD circuit setup.
    pub fn placeholder(input_len: usize) -> Self {
        Self {
            r1cs_input: vec![G::ScalarField::zero(); input_len],
            comm_a: G::zero(),
            comm_b: G::zero(),
            comm_c: G::zero(),
            hp_instance: HPInputInstance::<G>::zero(),
        }
    }
}

impl<G: AffineCurve + Absorb> Absorb for AccumulatorInstance<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        );
        dest.extend(tmp);
    }
}

/// The [`AccumulatorWitness`][acc_witness] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [acc_witness]: crate::AccumulationScheme::AccumulatorWitness
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitness<F: Field> {
    /// The R1CS witness with randomness applied if zero-knowledge is needed.
    pub(crate) r1cs_blinded_witness: Vec<F>,

    /// The Hadamard product accumulation scheme input witness.
    pub(crate) hp_witness: HPInputWitness<F>,

    /// Randomness for the Pedersen commitments to the linear combinations.
    pub(crate) randomness: Option<AccumulatorWitnessRandomness<F>>,
}

/// The randomness for the Pedersen commitments to the linear combinations.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct AccumulatorWitnessRandomness<F: Field> {
    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `A` matrix.
    pub(crate) sigma_a: F,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `B` matrix.
    pub(crate) sigma_b: F,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `C` matrix.
    pub(crate) sigma_c: F,
}

/// The [`Proof`][proof] of the [`ASForR1CSNark`][as_for_r1cs_nark].
///
/// [proof]: crate::AccumulationScheme::Proof
/// [as_for_r1cs_nark]: crate::r1cs_nark_as::ASForR1CSNark
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// The Hadamard product accumulation scheme proof.
    pub(crate) hp_proof: HPProof<G>,

    /// Randomness or their commitments used to blind the vectors of the indexed relation.
    pub(crate) randomness: Option<ProofRandomness<G>>,
}

impl<G: AffineCurve> Proof<G> {
    /// Outputs a placeholder for a proof to be used in the PCD circuit setup.
    pub fn placeholder(
        r1cs_input_len: usize,
        num_accumulators_and_inputs: usize,
        make_zk: bool,
    ) -> Self {
        let randomness = if make_zk {
            Some(ProofRandomness {
                r1cs_r_input: vec![G::ScalarField::zero(); r1cs_input_len],
                comm_r_a: G::zero(),
                comm_r_b: G::zero(),
                comm_r_c: G::zero(),
            })
        } else {
            None
        };

        // Accounts for the default case.
        let mut num_inputs = num_accumulators_and_inputs;
        if num_inputs == 0 {
            num_inputs += 1;
        }

        // Accounts for the addition dummy input added to HP_AS for zero knowledge.
        if num_inputs == 1 && make_zk {
            num_inputs += 1;
        }

        let hp_proof = HPProof::<G> {
            product_poly_comm: ProductPolynomialCommitment {
                low: vec![G::zero(); num_inputs - 1],
                high: vec![G::zero(); num_inputs - 1],
            },

            hiding_comms: if make_zk {
                Some(ProofHidingCommitments {
                    comm_1: G::zero(),
                    comm_2: G::zero(),
                    comm_3: G::zero(),
                })
            } else {
                None
            },
        };

        Self {
            hp_proof,
            randomness,
        }
    }
}

/// The randomness or their commitments used to blind the vectors of the indexed relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProofRandomness<G: AffineCurve> {
    /// Randomness used to blind the R1CS input.
    pub(crate) r1cs_r_input: Vec<G::ScalarField>,

    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: G,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: G,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: G,
}

impl<G: AffineCurve + Absorb> Absorb for ProofRandomness<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        );
        dest.extend(tmp);
    }
}
