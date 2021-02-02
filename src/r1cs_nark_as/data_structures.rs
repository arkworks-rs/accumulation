use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness, Proof as HPProof,
};
use crate::hp_as::HPAidedAccumulationScheme;
use crate::r1cs_nark::data_structures::{FirstRoundMessage, SecondRoundMessage};
use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_poly_commit::pedersen::CommitterKey as PedersenCommitmentCK;
use ark_relations::r1cs::Matrix;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::io::{Read, Write};

#[derive(Clone)]
pub struct PredicateIndex<F: Field> {
    /// The A matrix for the R1CS instance.
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<F>,

    pub index: usize,
}

#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// The A matrix for the R1CS instance.
    pub a: Matrix<G::ScalarField>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<G::ScalarField>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<G::ScalarField>,

    /// Hash of the matrices.
    pub as_matrices_hash: [u8; 32],

    /// Hash of the matrices.
    pub nark_matrices_hash: [u8; 32],

    pub index: usize,

    /// HP_AS pk
    pub ck: PedersenCommitmentCK<G>,
}

#[derive(Clone)]
pub struct VerifierKey {
    /// Hash of the matrices.
    pub as_matrices_hash: [u8; 32],

    /// Hash of the matrices.
    pub nark_matrices_hash: [u8; 32],

    /// Serves as HP_AS vk
    pub index: usize,
}

#[derive(Clone)]
pub struct DeciderKey<G: AffineCurve> {
    /// The A matrix for the R1CS instance.
    pub a: Matrix<G::ScalarField>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<G::ScalarField>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<G::ScalarField>,

    pub index: usize,

    /// HP_AS dk
    pub ck: PedersenCommitmentCK<G>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    pub r1cs_input: Vec<G::ScalarField>,
    pub first_round_message: FirstRoundMessage<G>,
    pub make_zk: bool,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    pub second_round_message: SecondRoundMessage<F>,
    pub make_zk: bool,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorInstance<G: AffineCurve> {
    pub r1cs_input: Vec<G::ScalarField>,
    pub comm_a: G,
    pub comm_b: G,
    pub comm_c: G,
    pub hp_instance: HPInputInstance<G>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitness<F: Field> {
    pub r1cs_blinded_witness: Vec<F>,
    pub hp_witness: HPInputWitness<F>,
    pub randomness: Option<AccumulatorWitnessRandomness<F>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitnessRandomness<F: Field> {
    pub sigma_a: F,
    pub sigma_b: F,
    pub sigma_c: F,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    pub hp_proof: HPProof<G>,
    pub randomness: Option<ProofRandomness<G>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofRandomness<G: AffineCurve> {
    pub r1cs_r_input: Vec<G::ScalarField>,
    pub comm_r_a: G,
    pub comm_r_b: G,
    pub comm_r_c: G,
}
