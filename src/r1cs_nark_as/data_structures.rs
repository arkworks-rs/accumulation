use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness, Proof as HPProof,
};
use crate::r1cs_nark::data_structures::{
    FirstRoundMessage, IndexInfo, IndexProverKey, SecondRoundMessage,
};
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField};
use ark_relations::r1cs::{Matrix, ToConstraintField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{Absorbable, DomainSeparator};
use ark_std::io::{Read, Write};

#[derive(Clone)]
pub struct PredicateIndex<F: Field> {
    /// The A matrix for the R1CS instance.
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<F>,

    pub index: usize,
}

#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// Underlying NARK prover key
    pub nark_pk: IndexProverKey<G>,

    /// Hash of the matrices for the accumulation scheme.
    pub as_matrices_hash: [u8; 32],
}

#[derive(Clone)]
pub struct VerifierKey {
    /// Underlying NARK infex
    pub nark_index: IndexInfo,

    /// Hash of the matrices for the accumulation scheme.
    pub as_matrices_hash: [u8; 32],
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    pub r1cs_input: Vec<G::ScalarField>,
    pub first_round_message: FirstRoundMessage<G>,
    pub make_zk: bool,
}

impl<CF, G> Absorbable<CF> for InputInstance<G>
where
    CF: PrimeField,
    G: AffineCurve + ToConstraintField<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut output = to_bytes!(self.r1cs_input).unwrap();
        output.append(&mut self.first_round_message.to_sponge_bytes());
        output.push(self.make_zk as u8);
        output
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output = to_bytes!(self.r1cs_input)
            .unwrap()
            .to_field_elements()
            .unwrap();
        output.append(&mut self.first_round_message.to_sponge_field_elements());
        output.push(CF::from(self.make_zk));

        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    pub second_round_message: SecondRoundMessage<F>,
    pub make_zk: bool,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorInstance<G: AffineCurve> {
    pub r1cs_input: Vec<G::ScalarField>,
    pub comm_a: G,
    pub comm_b: G,
    pub comm_c: G,
    pub hp_instance: HPInputInstance<G>,
}

impl<CF, G> Absorbable<CF> for AccumulatorInstance<G>
where
    CF: PrimeField,
    G: AffineCurve + ToConstraintField<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut output = to_bytes!(self.r1cs_input).unwrap();
        output.append(&mut to_bytes![self.comm_a, self.comm_b, self.comm_c].unwrap());

        output.append(&mut self.hp_instance.to_sponge_bytes());
        output
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output = to_bytes!(self.r1cs_input)
            .unwrap()
            .to_field_elements()
            .unwrap();

        output.append(&mut self.comm_a.to_field_elements().unwrap());
        output.append(&mut self.comm_b.to_field_elements().unwrap());
        output.append(&mut self.comm_c.to_field_elements().unwrap());
        output.append(&mut self.hp_instance.to_sponge_field_elements());

        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitnessRandomness<F: Field> {
    pub sigma_a: F,
    pub sigma_b: F,
    pub sigma_c: F,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulatorWitness<F: Field> {
    pub r1cs_blinded_witness: Vec<F>,
    pub hp_witness: HPInputWitness<F>,
    pub randomness: Option<AccumulatorWitnessRandomness<F>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofRandomness<G: AffineCurve> {
    pub r1cs_r_input: Vec<G::ScalarField>,
    pub comm_r_a: G,
    pub comm_r_b: G,
    pub comm_r_c: G,
}

impl<CF, G> Absorbable<CF> for ProofRandomness<G>
where
    CF: PrimeField,
    G: AffineCurve + ToConstraintField<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut output = to_bytes!(self.r1cs_r_input).unwrap();
        output.append(&mut to_bytes![self.comm_r_a, self.comm_r_b, self.comm_r_c].unwrap());
        output
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output = to_bytes!(self.r1cs_r_input)
            .unwrap()
            .to_field_elements()
            .unwrap();

        output.append(&mut self.comm_r_a.to_field_elements().unwrap());
        output.append(&mut self.comm_r_b.to_field_elements().unwrap());
        output.append(&mut self.comm_r_c.to_field_elements().unwrap());
        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    pub hp_proof: HPProof<G>,
    pub randomness: Option<ProofRandomness<G>>,
}

pub struct SimpleNARKDomain {}
impl DomainSeparator for SimpleNARKDomain {
    fn domain() -> Vec<u8> {
        crate::r1cs_nark::PROTOCOL_NAME.to_vec()
    }
}

pub struct SimpleNARKVerifierASDomain {}
impl DomainSeparator for SimpleNARKVerifierASDomain {
    fn domain() -> Vec<u8> {
        crate::r1cs_nark_as::PROTOCOL_NAME.to_vec()
    }
}
