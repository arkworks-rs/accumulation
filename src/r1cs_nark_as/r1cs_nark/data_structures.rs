use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_poly_commit::pedersen_pc::CommitterKey;
use ark_relations::r1cs::Matrix;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};
use ark_std::vec::Vec;

/// The public parameters of this NARK.
pub type PublicParameters = ();

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Clone, Copy)]
pub(crate) struct IndexInfo {
    /// The total number of variables in the constraint system.
    pub(crate) num_variables: usize,

    /// The number of constraints.
    pub(crate) num_constraints: usize,

    /// The number of public input (i.e. instance) variables.
    pub(crate) num_instance_variables: usize,

    /// Hash of the matrices.
    pub(crate) matrices_hash: [u8; 32],
}

/// The index prover key for our NARK.
#[derive(Clone)]
pub struct IndexProverKey<G: AffineCurve> {
    /// Information about the index.
    pub(crate) index_info: IndexInfo,

    /// The `A` matrix of the R1CS instance.
    pub(crate) a: Matrix<G::ScalarField>,

    /// The `B` matrix of the R1CS instance.
    pub(crate) b: Matrix<G::ScalarField>,

    /// The `C` matrix of the R1CS instance.
    pub(crate) c: Matrix<G::ScalarField>,

    /// Group elements required by the Pedersen commitment.
    pub(crate) ck: CommitterKey<G>,
}

/// Index verifier key for our NARK.
pub type IndexVerifierKey<G> = IndexProverKey<G>;

/// The sigma protocol's prover commitment.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FirstRoundMessage<G: AffineCurve> {
    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: G,

    /// Pedersen commitment to the `Bz` vector.
    pub(crate) comm_b: G,

    /// Pedersen commitment to the `Cz` vector.
    pub(crate) comm_c: G,

    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: Option<G>,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: Option<G>,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: Option<G>,

    /// Pedersen commitment to the first cross term randomness vector
    pub(crate) comm_1: Option<G>,

    /// Pedersen commitment to the second cross term randomness vector
    pub(crate) comm_2: Option<G>,
}

impl<CF, G> Absorbable<CF> for FirstRoundMessage<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        )
    }
}

/// The sigma protocol's prover response.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SecondRoundMessage<F: Field> {
    /// The R1CS witness with randomness applied if zero-knowledge is needed.
    pub(crate) blinded_witness: Vec<F>,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `A` matrix.
    pub(crate) sigma_a: Option<F>,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `B` matrix.
    pub(crate) sigma_b: Option<F>,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `C` matrix.
    pub(crate) sigma_c: Option<F>,

    /// The blinded randomness for the Pedersen commitment to the cross terms
    pub(crate) sigma_o: Option<F>,
}

/// The proof for our NARK.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// The sigma protocol's prove commitment.
    pub(crate) first_msg: FirstRoundMessage<G>,

    /// The sigma protocol's prove response.
    pub(crate) second_msg: SecondRoundMessage<G::ScalarField>,

    /// The zero-knowledge configuration.
    pub(crate) make_zk: bool,
}
