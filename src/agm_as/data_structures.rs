use crate::std::vec::Vec;
use ark_ec::PairingEngine;
use ark_ff::to_bytes;
use ark_poly_commit::marlin_pc::MarlinKZG10;
use ark_poly_commit::{marlin_pc, LabeledCommitment, PolynomialCommitment};
use ark_sponge::Absorbable;

/// The index of the AS_AGM predicate, which is the index of the PC_AGM relation.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct PredicateIndex {
    /// The supported degree by the PC_AGM index.
    pub supported_degree: usize,

    /// The hiding bound supported by the PC_AGM index.
    pub supported_hiding_bound: usize,

    /// The degree bounds that are supported by the PC_AGM index.
    pub enforced_degree_bounds: Option<Vec<usize>>,
}

/// An instance of the PC_AGM relation.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct AGMInstance<E: PairingEngine> {
    /// The PC_AGM commitment to the polynomial.
    pub commitment: LabeledCommitment<marlin_pc::Commitment<E>>,

    /// The degree bound to the polynomial.
    /// If this value is None, then degree bounds are not enforced for the polynomial.
    pub degree_bound: Option<usize>,

    /// The point opened for the polynomial.
    pub point: E::Fr,

    /// The evaluation of the polynomial at `point`.
    pub evaluation: E::Fr,
}

impl<E: PairingEngine> Absorbable<E::Fr> for AGMInstance<E> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![
            self.commitment,
            self.degree_bound.map(|d| d.to_le_bytes()),
            self.point,
            self.evaluation
        ]
        .unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fr> {
        self.to_sponge_bytes().to_sponge_field_elements()
    }
}

/// A single input of the AS_AGM scheme, which is the instance and proof of the PC_AGM relation.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct InputInstance<E: PairingEngine> {
    /// The PC_AGM instance.
    pub instance: AGMInstance<E>,

    /// The PC_AGM proof.
    pub proof: <MarlinKZG10<E> as PolynomialCommitment<E::Fr>>::Proof,
}

impl<E: PairingEngine> Absorbable<E::Fr> for InputInstance<E> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut output = self.instance.to_sponge_bytes();
        output.extend(to_bytes!(self.proof).unwrap());
        output
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fr> {
        self.to_sponge_bytes().to_sponge_field_elements()
    }
}

/// An accumulator of the AS_AGM scheme and represents the accumulated inputs.
#[derive(Derivative)]
#[derivative(Clone, Eq, PartialEq)]
pub struct AccumulatorInstance<E: PairingEngine> {
    pub(crate) accumulated_commitments: E::G1Affine,
    pub(crate) accumulated_proofs: E::G1Affine,
}

impl<E: PairingEngine> Absorbable<E::Fr> for AccumulatorInstance<E> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![self.accumulated_commitments, self.accumulated_proofs].unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fr> {
        self.to_sponge_bytes().to_sponge_field_elements()
    }
}

/// A proof attesting that an accumulator for the AS_AGM scheme was properly computed.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct Proof<E: PairingEngine> {
    pub(crate) accumulated_commitments_randomness: E::G1Affine,
    pub(crate) accumulated_proofs_randomness: E::G1Affine,
}

impl<E: PairingEngine> Absorbable<E::Fr> for Proof<E> {
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![
            self.accumulated_commitments_randomness,
            self.accumulated_proofs_randomness
        ]
        .unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fr> {
        self.to_sponge_bytes().to_sponge_field_elements()
    }
}

/// A prover key of the AS_AGM scheme for accumulating inputs and old accumulators and producing
/// a proof attesting that the accumulator was computed correctly.
#[derive(Derivative)]
#[derivative(Clone)]
pub struct ProverKey<E: PairingEngine> {
    pub(crate) marlin_vk: marlin_pc::VerifierKey<E>,
    pub(crate) beta_g: E::G1Affine,
}
