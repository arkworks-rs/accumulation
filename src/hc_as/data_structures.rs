use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, PrimeField};
use ark_poly_commit::{lh_pc, LabeledCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    pub commitment: LabeledCommitment<lh_pc::Commitment<G>>,
    pub point: G::ScalarField,
    pub eval: G::ScalarField,
}

impl<G: AffineCurve + Absorbable<CF>, CF: PrimeField> Absorbable<CF> for InputInstance<G> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            self.commitment.commitment().0 .0,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.eval).unwrap()
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            self.commitment.commitment().0 .0,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.eval).unwrap()
        )
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleProof<G: AffineCurve> {
    pub(crate) witness_commitment: LabeledCommitment<lh_pc::Commitment<G>>,
    pub(crate) witness_eval: G::ScalarField,
    pub(crate) eval: G::ScalarField,
}

pub type Proof<G> = Vec<SingleProof<G>>;
