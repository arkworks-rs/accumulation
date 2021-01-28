use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
};
use crate::hp_as::HPAidedAccumulationScheme;
use ark_ec::AffineCurve;
use ark_poly_commit::pedersen::CommitterKey as PedersenCommitmentCK;
use ark_relations::r1cs::Matrix;
use ark_ff::Field;
use crate::r1cs_nark::data_structures::{FirstRoundMessage, SecondRoundMessage};

pub struct PredicateIndex<F: Field> {
    /// The A matrix for the R1CS instance.
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<F>,

    pub index: usize,
}

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

pub struct VerifierKey {
    /// Hash of the matrices.
    pub as_matrices_hash: [u8; 32],

    /// Hash of the matrices.
    pub nark_matrices_hash: [u8; 32],

    /// Serves as HP_AS vk
    pub index: usize,
}

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

pub struct InputInstance<G: AffineCurve> {
    pub first_round_message: FirstRoundMessage<G>,
    pub make_zk: bool,
}

pub struct InputWitness<F: Field> {
    pub second_round_message: SecondRoundMessage<F>,
    pub make_zk: bool,
}

pub struct AccumulatorInstance<G: AffineCurve> {
    pub r1cs_input: Vec<G::ScalarField>,
    pub comm_a: G,
    pub comm_b: G,
    pub comm_c: G,
    pub hp_instance: HPInputInstance<G>,
}

pub struct AccumulatorWitness<F: Field> {
    pub blinded_witness: Vec<F>,
    pub randomness: Option<(F, F, F)>,
    pub hp_witness: HPInputWitness<F>,
}
