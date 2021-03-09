use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{ipa_pc, LabeledCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::domain_separated::DomainSeparator;
use ark_std::io::{Read, Write};

/// The [`PredicateIndex`][predicate_index] of the [`InnerProductArgAtomicAS`][ipa_as].
///
/// [predicate_index]: crate::AccumulationScheme::PredicateIndex
/// [ipa_as]: crate::ipa_as::InnerProductArgAtomicAS
#[derive(Clone)]
pub struct PredicateIndex {
    /// The degree bound supported by IPA_PC.
    pub supported_degree_bound: usize,

    /// The hiding bound supported by IPA_PC.
    pub supported_hiding_bound: usize,
}

/// The [`InputInstance`][input_instance] of the [`InnerProductArgAtomicAS`][ipa_as].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [ipa_as]: crate::ipa_as::InnerProductArgAtomicAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// The IPA_PC commitment that will be or has been accumulated
    pub ipa_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,

    /// Point where the proof was opened at.
    pub point: G::ScalarField,

    /// Evaluation of the committed polynomial at the point.
    pub evaluation: G::ScalarField,

    /// The IPA_PC proof of evaluation at the point.
    pub ipa_proof: ipa_pc::Proof<G>,
}

/// The randomness to be accumulated with the inputs and to commit to polynomials.
/// If used, the randomness is the  [`Proof`][proof] of the [`InnerProductArgAtomicAS`][ipa_as].
///
/// [Proof]: crate::AccumulationScheme::Proof
/// [ipa_as]: crate::ipa_as::InnerProductArgAtomicAS
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Randomness<G: AffineCurve> {
    /// A random linear polynomial to be accumulated with the other input polynomials to apply
    /// zero-knowledge.
    pub(crate) random_linear_polynomial: DensePolynomial<G::ScalarField>,

    /// Commitment to the random linear polynomial.
    pub(crate) random_linear_polynomial_commitment: G,

    /// Randomness used to commit to the linear combination of the input polynomials.
    pub(crate) commitment_randomness: G::ScalarField,
}

/// The [`ProverKey`][pk] of the [`InnerProductArgAtomicAS`][ipa_as].
///
/// [pk]: crate::AccumulationScheme::ProverKey
/// [ipa_as]: crate::ipa_as::InnerProductArgAtomicAS
#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// The IPA_PC committer key for inputs.
    pub(crate) ipa_ck: ipa_pc::CommitterKey<G>,

    /// The accumulation scheme's [`VerifierKey`].
    pub(crate) verifier_key: VerifierKey<G>,
}

/// The [`VerifierKey`][vk] of the [`InnerProductArgAtomicAS`][ipa_as].
///
/// [vk]: crate::AccumulationScheme::VerifierKey
/// [ipa_as]: crate::ipa_as::InnerProductArgAtomicAS
#[derive(Clone)]
pub struct VerifierKey<G: AffineCurve> {
    /// The IPA_PC verifier key for inputs.
    pub(crate) ipa_vk: ipa_pc::VerifierKey<G>,

    /// The IPA_PC committer key for random linear polynomials.
    pub(crate) ipa_ck_linear: ipa_pc::CommitterKey<G>,
}

pub(crate) struct IpaPCDomain {}
impl DomainSeparator for IpaPCDomain {
    fn domain() -> Vec<u8> {
        b"PC-IPA-in-AS-IPA-2020".to_vec()
    }
}

pub(crate) struct IpaASDomain {}
impl DomainSeparator for IpaASDomain {
    fn domain() -> Vec<u8> {
        b"AS-IPA-2020".to_vec()
    }
}
