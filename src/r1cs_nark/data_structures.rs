use ark_ec::AffineCurve;
use ark_poly_commit::pedersen::*;
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

/// The index prover key for our NARK.
#[derive(Clone)]
pub struct IndexProverKey<G: AffineCurve> {
    /// Information about the index.
    pub index_info: IndexInfo,

    /// The A matrix for the R1CS instance.
    pub a: Matrix<G::ScalarField>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<G::ScalarField>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<G::ScalarField>,

    /// The group elements required by the Pedersen commitment.
    pub ck: CommitterKey<G>,
}

/// Index verifier key for our NARK. 
pub type IndexVerifierKey<G> = IndexProverKey<G>;

pub struct FirstRoundMessage<G: AffineCurve> {
    pub comm_a: Commitment<G>,
    pub comm_b: Commitment<G>,
    pub comm_c: Commitment<G>,
    pub comm_r_a: Option<Commitment<G>>,
    pub comm_r_b: Option<Commitment<G>>,
    pub comm_r_c: Option<Commitment<G>>,
    pub comm_1: Option<Commitment<G>>,
    pub comm_2: Option<Commitment<G>>,
}

pub struct SecondRoundMessage<F: Field> {
    pub blinded_witness: Vec<F>,
    pub sigma_a: Option<F>,
    pub sigma_b: Option<F>,
    pub sigma_c: Option<F>,
    pub sigma_o: Option<F>,
}

/// The proof for our NARK.
pub struct Proof<G: AffineCurve> {
    pub first_msg: FirstRoundMessage<G>,
    pub second_msg: SecondRoundMessage<G::ScalarField>,
}