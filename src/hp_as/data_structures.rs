use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorb};
use ark_std::io::{Read, Write};
use ark_std::vec;
use ark_std::vec::Vec;

/// The [`InputInstance`][input_instance] of the [`ASForHadamardProducts`][as_for_hp].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [as_for_hp]: crate::hp_as::ASForHadamardProducts
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct InputInstance<G: AffineCurve> {
    /// Pedersen commitment to the `a` vector of the Hadamard product relation.
    pub comm_1: G,

    /// Pedersen commitment to the `b` vector of the Hadamard product relation.
    pub comm_2: G,

    /// Pedersen commitment to the `a ◦ b` vector of the Hadamard product relation.
    pub comm_3: G,
}

impl<G: AffineCurve> InputInstance<G> {
    pub(crate) fn zero() -> Self {
        Self {
            comm_1: G::zero(),
            comm_2: G::zero(),
            comm_3: G::zero(),
        }
    }
}

impl<G: AffineCurve + Absorb> Absorb for InputInstance<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        dest = &mut collect_sponge_bytes!(self.comm_1, self.comm_2, self.comm_3);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        dest = &mut collect_sponge_field_elements!(self.comm_1, self.comm_2, self.comm_3);
    }
}

/// The [`InputWitness`][input_witness] of the [`ASForHadamardProducts`][as_for_hp].
///
/// [input_witness]: crate::AccumulationScheme::InputWitness
/// [as_for_hp]: crate::hp_as::ASForHadamardProducts
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    /// The `a` vector of the Hadamard product relation.
    pub a_vec: Vec<F>,

    /// The `b` vector of the Hadamard product relation.
    pub b_vec: Vec<F>,

    /// Randomness used to compute hiding commitments for zero-knowledge.
    pub randomness: Option<InputWitnessRandomness<F>>,
}

impl<F: Field> InputWitness<F> {
    pub(crate) fn zero(vec_len: usize) -> Self {
        Self {
            a_vec: vec![F::zero(); vec_len],
            b_vec: vec![F::zero(); vec_len],
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

    /// Randomness used to commit the cross term randomness vector.
    pub rand_3: F,
}

/// The [`Proof`][proof] of the [`ASForHadamardProducts`][as_for_hp].
///
/// [proof]: crate::AccumulationScheme::Proof
/// [as_for_hp]: crate::hp_as::ASForHadamardProducts
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    /// Pedersen commitments to each coefficient vector of the product polynomial
    /// `a(X, µ) ◦ b(X)`, excluding `n-1`th coefficient (0-index)
    pub(crate) product_poly_comm: ProductPolynomialCommitment<G>,

    /// Pedersen commitments to the random vectors used to apply zero-knowledge to the vectors
    /// of the Hadamard product relation.
    pub(crate) hiding_comms: Option<ProofHidingCommitments<G>>,
}

/// The Pedersen commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
/// Excludes `n-1`th commitment (0-index)
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProductPolynomialCommitment<G: AffineCurve> {
    /// Pedersen commitments to the first `n-1` coefficients of the lower powers.
    pub(crate) low: Vec<G>,

    /// Pedersen commitments to the last `n-1` coefficients of the higher powers.
    pub(crate) high: Vec<G>,
}

impl<G: AffineCurve + Absorb> Absorb for ProductPolynomialCommitment<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        dest = &mut collect_sponge_bytes!(self.low, self.high);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        dest = &mut collect_sponge_field_elements!(self.low, self.high);
    }
}

/// The Pedersen commitments to the random vectors used to apply zero-knowledge to the vectors of
/// the Hadamard product relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct ProofHidingCommitments<G: AffineCurve> {
    /// Pedersen commitment to the random vector that hides the `a` vector of the Hadamard
    /// product relation.
    pub(crate) comm_1: G,

    /// Pedersen commitment to the random vector that hides the `b` vector of the Hadamard
    /// product relation.
    pub(crate) comm_2: G,

    /// Pedersen commitment to the cross term randomness vector
    pub(crate) comm_3: G,
}

impl<G: AffineCurve + Absorb> Absorb for ProofHidingCommitments<G> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        dest = &mut collect_sponge_bytes!(self.comm_1, self.comm_2, self.comm_3);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        dest = &mut collect_sponge_field_elements!(self.comm_1, self.comm_2, self.comm_3);
    }
}
