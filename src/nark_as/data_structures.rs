use crate::hp_as::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness, Proof as HPProof,
};
use crate::nark_as;
use crate::nark_as::r1cs_nark;
use crate::nark_as::r1cs_nark::{FirstRoundMessage, IndexInfo, IndexProverKey, SecondRoundMessage};
use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField};
use ark_relations::r1cs::{Matrix, ToConstraintField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::domain_separated::DomainSeparator;
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
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
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message,
            self.make_zk
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.first_round_message,
            self.make_zk
        )
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
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_input).unwrap(),
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        )
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
    G: AffineCurve + Absorbable<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            CF,
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        collect_sponge_field_elements!(
            to_bytes!(self.r1cs_r_input).unwrap(),
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        )
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
        r1cs_nark::PROTOCOL_NAME.to_vec()
    }
}

pub struct SimpleNARKVerifierASDomain {}
impl DomainSeparator for SimpleNARKVerifierASDomain {
    fn domain() -> Vec<u8> {
        nark_as::PROTOCOL_NAME.to_vec()
    }
}
