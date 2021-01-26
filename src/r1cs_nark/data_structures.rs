use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_relations::r1cs::*;

/// The public parameters of this NARK.
pub type PublicParameters = ();

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Clone, Copy)]
pub struct IndexInfo {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The number of public input (i.e. instance) variables.
    pub num_instance_variables: usize,
    /// Hash of the matrices.
    pub matrices_hash: [u8; 32],
}

/// The index for our NARK.
pub struct Index<G: AffineCurve> {
    /// Information about the index.
    pub index_info: IndexInfo,

    /// The A matrix for the R1CS instance.
    pub a: Matrix<G::ScalarField>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<G::ScalarField>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<G::ScalarField>,

    /// The group elements required by the Pedersen commitment.
    pub ck: Vec<G>,
}

pub struct SigmaProtocolCommitment<G: AffineCurve> {
    pub comm_a: G,
    pub comm_b: G,
    pub comm_c: G,
    pub comm_rand_a: G,
    pub comm_rand_b: G,
    pub comm_rand_c: G,
    pub comm_1: G,
    pub comm_2: G,
}

pub struct SigmaProtocolResponse<G: AffineCurve> {
    pub blinded_witness: Vec<G::ScalarField>,
    pub blinded_lin_comb_rand: G::ScalarField,
    pub blinded_cross_term_rand: G::ScalarField,
}

/// The proof for our NARK.
pub struct Proof<G: AffineCurve> {
    comm_a: G
}