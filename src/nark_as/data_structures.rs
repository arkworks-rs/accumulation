use crate::hp_as::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness, Proof as HPProof,
};
use crate::nark_as::r1cs_nark::{FirstRoundMessage, IndexInfo, IndexProverKey, SecondRoundMessage};
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField};
use ark_relations::r1cs::Matrix;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};

/// The [`PredicateIndex`][predicate_index] of the [`NarkAS`][nark_as].
///
/// [predicate_index]: crate::AccumulationScheme::PredicateIndex
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone)]
pub struct PredicateIndex<F: Field> {
    /// The `A` matrix for the R1CS instance.
    pub a: Matrix<F>,

    /// The `B` matrix for the R1CS instance.
    pub b: Matrix<F>,

    /// The `C` matrix for the R1CS instance.
    pub c: Matrix<F>,

    /// The index of the relation verified by the NARK.
    pub index: usize,
}

/// The [`ProverKey`][pk] of the [`NarkAS`][nark_as].
///
/// [pk]: crate::AccumulationScheme::ProverKey
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// The underlying NARK prover key
    pub(crate) nark_pk: IndexProverKey<G>,

    /// The hash of the matrices for the accumulation scheme.
    pub(crate) as_matrices_hash: [u8; 32],
}

/// The [`VerifierKey`][vk] of the [`NarkAS`][nark_as].
///
/// [vk]: crate::AccumulationScheme::VerifierKey
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone)]
pub struct VerifierKey {
    /// The underlying NARK index
    pub(crate) nark_index: IndexInfo,

    /// The hash of the matrices for the accumulation scheme.
    pub(crate) as_matrices_hash: [u8; 32],
}

/// The [`InputInstance`][input_instance] of the [`NarkAS`][nark_as].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// The R1CS input for the indexed relation.
    pub r1cs_input: Vec<G::ScalarField>,

    /// The sigma protocol's prover commitment of the NARK.
    pub first_round_message: FirstRoundMessage<G>,

    /// The zero-knowledge configuration.
    pub make_zk: bool,
}

impl<CF, G> Absorbable<CF> for InputInstance<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message,
            self.make_zk
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message,
            self.make_zk
        )
    }
}

/// The [`InputWitness`][input_witness] of the [`NarkAS`][nark_as].
///
/// [input_witness]: crate::AccumulationScheme::InputWitness
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    /// The sigma protocol's prover commitment of the NARK.
    pub second_round_message: SecondRoundMessage<F>,

    /// The zero-knowledge configuration.
    pub make_zk: bool,
}

/// The [`AccumulatorInstance`][acc_instance] of the [`NarkAS`][nark_as].
///
/// [acc_instance]: crate::AccumulationScheme::AccumulatorInstance
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorInstance<G: AffineCurve> {
    /// An input for the indexed relation.
    pub(crate) r1cs_input: Vec<G::ScalarField>,

    /// Commitment to the `Az` vector.
    pub(crate) comm_a: G,

    /// Commitment to the `Bz` vector.
    pub(crate) comm_b: G,

    /// Commitment to the `Cz` vector.
    pub(crate) comm_c: G,

    /// The Hadamard product accumulation scheme input instance
    pub(crate) hp_instance: HPInputInstance<G>,
}

impl<CF, G> Absorbable<CF> for AccumulatorInstance<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        )
    }
}

/// The randomness for the linear combinations of Pedersen commitment randomness
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct AccumulatorWitnessRandomness<F: Field> {
    /// Blinded randomness for the commitment to the linear combination used with the `A` matrix.
    pub(crate) sigma_a: F,

    /// Blinded randomness for the commitment to the linear combination used with the `B` matrix.
    pub(crate) sigma_b: F,

    /// Blinded randomness for the commitment to the linear combination used with the `C` matrix.
    pub(crate) sigma_c: F,
}

/// The [`AccumulatorWitness`][acc_witness] of the [`NarkAS`][nark_as].
///
/// [acc_witness]: crate::AccumulationScheme::AccumulatorWitness
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitness<F: Field> {
    /// The R1CS witness with randomness applied if zero-knowledge is needed.
    pub(crate) r1cs_blinded_witness: Vec<F>,

    /// The Hadamard product accumulation scheme input witness.
    pub(crate) hp_witness: HPInputWitness<F>,

    /// Randomness for the linear combinations of Pedersen commitment randomness
    pub(crate) randomness: Option<AccumulatorWitnessRandomness<F>>,
}

/// The randomness or their commitments used to blind the vectors of the indexed relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProofRandomness<G: AffineCurve> {
    /// Randomness used to blind the R1CS input.
    pub(crate) r1cs_r_input: Vec<G::ScalarField>,

    /// Commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: G,

    /// Commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: G,

    /// Commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: G,
}

impl<CF, G> Absorbable<CF> for ProofRandomness<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        )
    }
}

/// The [`Proof`][proof] of the [`NarkAS`][nark_as].
///
/// [proof]: crate::AccumulationScheme::Proof
/// [nark_as]: crate::nark_as::NarkAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// The Hadamard product accumulation scheme proof.
    pub(crate) hp_proof: HPProof<G>,

    /// The randomness or their commitments used to blind the vectors of the indexed relation.
    pub(crate) randomness: Option<ProofRandomness<G>>,
}
