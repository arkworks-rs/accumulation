use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_poly_commit::trivial_pc::CommitterKey;
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

/// The sigma protocol's prover commitment randomness.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FirstRoundMessageRandomness<G: AffineCurve> {
    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: G,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: G,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: G,

    /// Pedersen commitment to the first cross term randomness vector
    pub(crate) comm_1: G,

    /// Pedersen commitment to the second cross term randomness vector
    pub(crate) comm_2: G,
}

impl<CF, G> Absorbable<CF> for FirstRoundMessageRandomness<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        )
    }
}

/// The sigma protocol's prover commitment.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FirstRoundMessage<G: AffineCurve> {
    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: G,

    /// Pedersen commitment to the `Bz` vector.
    pub(crate) comm_b: G,

    /// Pedersen commitment to the `Cz` vector.
    pub(crate) comm_c: G,

    /// The randomness used for the commitment.
    pub(crate) randomness: Option<FirstRoundMessageRandomness<G>>,
}

impl<G: AffineCurve> FirstRoundMessage<G> {
    pub(crate) fn zero() -> Self {
        Self {
            comm_a: G::zero(),
            comm_b: G::zero(),
            comm_c: G::zero(),
            randomness: None,
        }
    }
}

impl<CF, G> Absorbable<CF> for FirstRoundMessage<G>
where
    CF: PrimeField,
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(CF, self.comm_a, self.comm_b, self.comm_c, self.randomness)
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(self.comm_a, self.comm_b, self.comm_c, self.randomness)
    }
}

/// The sigma protocol's prover response randomness.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SecondRoundMessageRandomness<F: Field> {
    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `A` matrix.
    pub(crate) sigma_a: F,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `B` matrix.
    pub(crate) sigma_b: F,

    /// The blinded randomness for the Pedersen commitment to the linear combination with the
    /// `C` matrix.
    pub(crate) sigma_c: F,

    /// The blinded randomness for the Pedersen commitment to the cross terms
    pub(crate) sigma_o: F,
}

/// The sigma protocol's prover response.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SecondRoundMessage<F: Field> {
    /// The R1CS witness with randomness applied if zero-knowledge is needed.
    pub(crate) blinded_witness: Vec<F>,

    /// The randomness used for the response.
    pub(crate) randomness: Option<SecondRoundMessageRandomness<F>>,
}

impl<F: Field> SecondRoundMessage<F> {
    pub(crate) fn zero(witness_len: usize) -> Self {
        Self {
            blinded_witness: vec![F::zero(); witness_len],
            randomness: None,
        }
    }
}

/// The proof for our NARK.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// The sigma protocol's prove commitment.
    pub(crate) first_msg: FirstRoundMessage<G>,

    /// The sigma protocol's prove response.
    pub(crate) second_msg: SecondRoundMessage<G::ScalarField>,
}
