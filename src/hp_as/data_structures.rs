use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::io::{Read, Write};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct InputInstance<G: AffineCurve> {
    pub comm_1: G,
    pub comm_2: G,
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

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputWitness<F: Field> {
    pub a_vec: Vec<F>,
    pub b_vec: Vec<F>,
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

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofHidingCommitments<G: AffineCurve> {
    pub comm_1: G,
    pub comm_2: G,
    pub comm_3: G,
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
