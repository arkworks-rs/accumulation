use ark_ec::AffineCurve;
use ark_ff::{to_bytes, PrimeField};
use ark_poly_commit::{trivial_pc, LabeledCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};
use ark_std::vec::Vec;

/// The [`InputInstance`][input_instance] of the [`ASForTrivialPC`][as_for_trivial_pc].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [as_for_trivial_pc]: crate::trivial_pc_as::ASForTrivialPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// Pedersen commitment to a polynomial.
    pub commitment: LabeledCommitment<trivial_pc::Commitment<G>>,

    /// Point where the proof was opened at.
    pub point: G::ScalarField,

    /// Evaluation of the committed polynomial at the point.
    pub eval: G::ScalarField,
}

impl<G: AffineCurve + Absorbable<CF>, CF: PrimeField> Absorbable<CF> for InputInstance<G> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            self.commitment.commitment().elem,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.eval).unwrap()
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            self.commitment.commitment().elem,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.eval).unwrap()
        )
    }
}

/// A proof attesting that a single [`Input`][input] of [`ASForTrivialPC`][as_for_trivial_pc] was
/// properly accumulated.
///
/// [input]: crate::Input
/// [as_for_trivial_pc]: crate::trivial_pc_as::ASForTrivialPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleProof<G: AffineCurve> {
    /// Pedersen commitment to the witness polynomial.
    pub(crate) witness_commitment: LabeledCommitment<trivial_pc::Commitment<G>>,

    /// Evaluation of the witness polynomial at the challenge point.
    pub(crate) witness_eval: G::ScalarField,

    /// Evaluation of the input polynomial at the challenge point.
    pub(crate) eval: G::ScalarField,
}

/// The list of [`SingleProof`]s for each accumulated input.
/// The [`Proof`][proof] of the [`ASForTrivialPC`][as_for_trivial_pc].
///
/// [proof]: crate::AccumulationScheme::Proof
/// [as_for_trivial_pc]: crate::trivial_pc_as::ASForTrivialPC
pub type Proof<G> = Vec<SingleProof<G>>;
