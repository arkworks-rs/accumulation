use ark_ff::PrimeField;
use ark_poly_commit::lh_pc::linear_hash::LinearHashFunction;
use ark_poly_commit::{lh_pc, LabeledCommitment, Polynomial};
use ark_sponge::Absorbable;

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField, LH: LinearHashFunction<F>"))]
pub struct ProverKey<F: PrimeField, LH: LinearHashFunction<F>> {
    pub(crate) lh_ck: lh_pc::CommitterKey<F, LH>,
    pub(crate) degree_challenge: F,
}

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField, LH: LinearHashFunction<F>"))]
pub struct InputInstance<F: PrimeField, LH: LinearHashFunction<F>> {
    pub commitment: LabeledCommitment<lh_pc::Commitment<F, LH>>,
    pub point: F,
    pub eval: F,
}

impl<F: PrimeField, LH: LinearHashFunction<F>> Absorbable<F> for InputInstance<F, LH> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn to_sponge_field_elements(&self) -> Vec<F> {
        unimplemented!()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField, LH: LinearHashFunction<F>"))]
pub struct SingleProof<F: PrimeField, LH: LinearHashFunction<F>> {
    pub(crate) witness_commitment: LabeledCommitment<lh_pc::Commitment<F, LH>>,
    pub(crate) witness_eval: F,
    pub(crate) eval: F,
}

pub type Proof<F, LH> = Vec<SingleProof<F, LH>>;
