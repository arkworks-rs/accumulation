use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{ipa_pc, LabeledCommitment, UVPolynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize, DomainSeparator};
use ark_std::io::{Read, Write};
use ark_std::marker::PhantomData;

#[derive(Clone)]
pub struct PredicateIndex {
    /// The degree bound supported by IPA_PC.
    pub supported_degree_bound: usize,

    /// The hiding bound supported by IPA_PC.
    pub supported_hiding_bound: usize,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// The IPA_PC commitment that will be or has been accumulated
    pub ipa_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,

    /// Point where the proof was opened at.
    pub point: G::ScalarField,

    /// The evaluation of the committed polynomial at the point.
    pub evaluation: G::ScalarField,

    /// The IPA_PC proof of evaluation at the point.
    pub ipa_proof: ipa_pc::Proof<G>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Randomness<G: AffineCurve> {
    pub(crate) random_linear_polynomial: DensePolynomial<G::ScalarField>,
    pub(crate) random_linear_polynomial_commitment: G,
    pub(crate) commitment_randomness: G::ScalarField,
}

#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    pub(crate) ipa_ck: ipa_pc::CommitterKey<G>,
    pub(crate) verifier_key: VerifierKey<G>,
}

#[derive(Clone)]
pub struct VerifierKey<G: AffineCurve> {
    pub(crate) ipa_vk: ipa_pc::VerifierKey<G>,
    pub(crate) ipa_ck_linear: ipa_pc::CommitterKey<G>,
}

pub struct PCDLDomain {}
impl DomainSeparator for PCDLDomain {
    fn domain() -> Vec<u8> {
        b"PC-DL-in-AS-DL-2020".to_vec()
    }
}

pub struct ASDLDomain {}
impl DomainSeparator for ASDLDomain {
    fn domain() -> Vec<u8> {
        b"AS_DL-2020".to_vec()
    }
}