use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};

/// The [`InputInstance`][input_instance] of the [`HadamardProductAS`][hp_as].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [hp_as]: crate::hp_as::HadamardProductAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct InputInstance<G: AffineCurve> {
    /// Commitment to the `a` vector of the Hadamard product relation.
    pub comm_1: G,

    /// Commitment to the `b` vector of the Hadamard product relation.
    pub comm_2: G,

    /// Commitment to the `a ◦ b` vector of the Hadamard product relation.
    pub comm_3: G,
}

impl<G: AffineCurve> Default for InputInstance<G> {
    fn default() -> Self {
        Self {
            comm_1: G::zero(),
            comm_2: G::zero(),
            comm_3: G::zero(),
        }
    }
}

impl<G, CF> Absorbable<CF> for InputInstance<G>
where
    G: AffineCurve + Absorbable<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(CF, self.comm_1, self.comm_2, self.comm_3)
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(self.comm_1, self.comm_2, self.comm_3)
    }
}

/// The [`InputWitness`][input_witness] of the [`HadamardProductAS`][hp_as].
///
/// [input_witness]: crate::AccumulationScheme::InputWitness
/// [hp_as]: crate::hp_as::HadamardProductAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    /// The `a` vector of the Hadamard product relation.
    pub a_vec: Vec<F>,

    /// The `b` vector of the Hadamard product relation.
    pub b_vec: Vec<F>,

    /// Randomness used to compute hiding commitments for zero-knowledge.
    pub randomness: Option<InputWitnessRandomness<F>>,
}

impl<F: Field> Default for InputWitness<F> {
    fn default() -> Self {
        Self {
            a_vec: vec![],
            b_vec: vec![],
            randomness: None,
        }
    }
}

/// The randomness used to compute hiding commitments for zero-knowledge.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitnessRandomness<F: Field> {
    /// Randomness used to commit the random vector that hides the `a` vector of the Hadamard
    /// product relation.
    pub rand_1: F,

    /// Randomness used to commit the random vector that hides the `b` vector of the Hadamard
    /// product relation.
    pub rand_2: F,

    /// Randomness used to commit the cross term randomness vector
    pub rand_3: F,
}

/// The [`Proof`][proof] of the [`HadamardProductAS`][hp_as].
///
/// [proof]: crate::AccumulationScheme::Proof
/// [hp_as]: crate::hp_as::HadamardProductAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// Commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
    /// Excludes `n-1`th commitment (0-index)
    pub(crate) t_comms: ProofTCommitments<G>,

    /// Commitments to the random vectors used to apply zero-knowledge to the vectors of the
    /// Hadamard product relation.
    pub(crate) hiding_comms: Option<ProofHidingCommitments<G>>,
}

/// The commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
/// Excludes `n-1`th commitment (0-index)
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProofTCommitments<G: AffineCurve> {
    /// The first `n-1` commitments.
    pub(crate) low: Vec<G>,

    /// The last `n-1` commitments.
    pub(crate) high: Vec<G>,
}

impl<G, CF> Absorbable<CF> for ProofTCommitments<G>
where
    G: AffineCurve + Absorbable<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(CF, self.low, self.high)
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(self.low, self.high)
    }
}

/// The commitments to the random vectors used to apply zero-knowledge to the vectors of the
/// Hadamard product relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProofHidingCommitments<G: AffineCurve> {
    /// Commitment to the random vector that hides the `a` vector of the Hadamard product relation.
    pub(crate) comm_1: G,

    /// Commitment to the random vector that hides the `b` vector of the Hadamard product relation.
    pub(crate) comm_2: G,

    /// Commitment to the cross term randomness vector
    pub(crate) comm_3: G,
}

impl<G, CF> Absorbable<CF> for ProofHidingCommitments<G>
where
    G: AffineCurve + Absorbable<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(CF, self.comm_1, self.comm_2, self.comm_3)
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(self.comm_1, self.comm_2, self.comm_3)
    }
}
