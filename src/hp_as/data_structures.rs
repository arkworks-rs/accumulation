use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField};
use ark_relations::r1cs::ToConstraintField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::Absorbable;
use ark_std::io::{Read, Write};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct InputInstance<G: AffineCurve> {
    pub comm_1: G,
    pub comm_2: G,
    pub comm_3: G,
}

impl<G, CF> Absorbable<CF> for InputInstance<G>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![self.comm_1, self.comm_2, self.comm_3].unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output: Vec<CF> = self.comm_1.to_field_elements().unwrap();
        output.append(&mut self.comm_2.to_field_elements().unwrap());
        output.append(&mut self.comm_3.to_field_elements().unwrap());
        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    pub a_vec: Vec<F>,
    pub b_vec: Vec<F>,
    pub randomness: Option<InputWitnessRandomness<F>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitnessRandomness<F: Field> {
    pub rand_1: F,
    pub rand_2: F,
    pub rand_3: F,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    pub t_comms: ProofTCommitments<G>,
    pub hiding_comms: Option<ProofHidingCommitments<G>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofTCommitments<G: AffineCurve> {
    pub low: Vec<G>,
    pub high: Vec<G>,
}

impl<G, CF> Absorbable<CF> for ProofTCommitments<G>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
{
    // TODO: Absorb size?
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut bytes = to_bytes!(self.low).unwrap();
        bytes.append(&mut to_bytes!(self.high).unwrap());
        bytes
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output: Vec<CF> = Vec::new();
        for t_comm in &self.low {
            output.append(&mut t_comm.to_field_elements().unwrap())
        }

        for t_comm in &self.high {
            output.append(&mut t_comm.to_field_elements().unwrap())
        }

        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofHidingCommitments<G: AffineCurve> {
    pub comm_1: G,
    pub comm_2: G,
    pub comm_3: G,
}

impl<G, CF> Absorbable<CF> for ProofHidingCommitments<G>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![self.comm_1, self.comm_2, self.comm_3].unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output: Vec<CF> = self.comm_1.to_field_elements().unwrap();
        output.append(&mut self.comm_2.to_field_elements().unwrap());
        output.append(&mut self.comm_3.to_field_elements().unwrap());
        output
    }
}
