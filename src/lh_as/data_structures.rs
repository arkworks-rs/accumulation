use crate::std::vec::Vec;
use ark_ff::{to_bytes, ToConstraintField};
use ark_ec::AffineCurve;
use ark_poly_commit::{lh_pc, LabeledCommitment};
use ark_sponge::Absorbable;
use ark_poly_commit::lh_pc::{CommitterKey, Commitment};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize, SerializationError};
use ark_std::io::{Read, Write};

#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    pub(crate) lh_ck: CommitterKey<G>,
    pub(crate) degree_challenge: G::ScalarField,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    pub commitment: LabeledCommitment<Commitment<G>>,
    pub point: G::ScalarField,
    pub eval: G::ScalarField,
}

impl<G: AffineCurve> Absorbable<G::ScalarField> for InputInstance<G> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes!(&self.commitment, &self.point, &self.eval).unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<G::ScalarField> {
        self.to_sponge_bytes().to_field_elements().unwrap()
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleProof<G: AffineCurve> {
    pub(crate) witness_commitment: LabeledCommitment<lh_pc::Commitment<G>>,
    pub(crate) witness_eval: G::ScalarField,
    pub(crate) eval: G::ScalarField,
}

pub type Proof<G> = Vec<SingleProof<G>>;
