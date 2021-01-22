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