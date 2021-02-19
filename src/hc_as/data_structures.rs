use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, PrimeField, ToConstraintField};
use ark_poly_commit::{lh_pc, LabeledCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::Absorbable;
use ark_std::io::{Read, Write};

#[derive(Clone)]
pub struct ProverKey<G: AffineCurve, CF: PrimeField> {
    pub(crate) lh_ck: lh_pc::CommitterKey<G>,
    pub(crate) degree_challenge: CF,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    pub commitment: LabeledCommitment<lh_pc::Commitment<G>>,
    pub point: G::ScalarField,
    pub eval: G::ScalarField,
}

impl<G: AffineCurve + ToConstraintField<CF>, CF: PrimeField> Absorbable<CF> for InputInstance<G> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes!(&self.commitment, &self.point, &self.eval).unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut field_elements: Vec<CF> = self
            .commitment
            .commitment()
            .0
             .0
            .to_field_elements()
            .unwrap();
        field_elements.append(&mut to_bytes!(self.point).unwrap().to_field_elements().unwrap());
        field_elements.append(&mut to_bytes!(self.eval).unwrap().to_field_elements().unwrap());
        field_elements
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleProof<G: AffineCurve> {
    pub(crate) witness_commitment: LabeledCommitment<lh_pc::Commitment<G>>,
    pub(crate) witness_eval: G::ScalarField,
    pub(crate) eval: G::ScalarField,
}

pub type Proof<G> = Vec<SingleProof<G>>;
