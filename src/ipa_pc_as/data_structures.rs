use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{ipa_pc, LabeledCommitment};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::domain_separated::DomainSeparator;
use ark_sponge::{Absorbable, CryptographicSponge};
use ark_std::io::{Read, Write};
use ark_std::vec::Vec;

/// The [`PredicateIndex`][predicate_index] of the [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [predicate_index]: crate::AccumulationScheme::PredicateIndex
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
#[derive(Clone)]
pub struct PredicateIndex {
    /// The degree bound supported by IpaPC.
    pub supported_degree_bound: usize,

    /// The hiding bound supported by IpaPC.
    pub supported_hiding_bound: usize,
}

/// The [`ProverKey`][pk] of the [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [pk]: crate::AccumulationScheme::ProverKey
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
#[derive(Clone)]
pub struct ProverKey<G: AffineCurve> {
    /// The IpaPC committer key for committing input polynomials.
    pub(crate) ipa_ck: ipa_pc::CommitterKey<G>,

    /// The accumulation scheme's [`VerifierKey`].
    pub(crate) verifier_key: VerifierKey<G>,
}

/// The [`VerifierKey`][vk] of the [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [vk]: crate::AccumulationScheme::VerifierKey
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
#[derive(Clone)]
pub struct VerifierKey<G: AffineCurve> {
    /// The IpaPC succinct check key for inputs.
    pub(crate) ipa_svk: ipa_pc::SuccinctVerifierKey<G>,

    /// The IpaPC committer key for random linear polynomials.
    pub(crate) ipa_ck_linear: ipa_pc::CommitterKey<G>,
}

/// The [`InputInstance`][input_instance] of the [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    /// The IpaPC commitment to a polynomial.
    pub ipa_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,

    /// Point where the proof was opened at.
    pub point: G::ScalarField,

    /// Evaluation of the committed polynomial at the point.
    pub evaluation: G::ScalarField,

    /// The IpaPC proof of evaluation at the point.
    pub ipa_proof: ipa_pc::Proof<G>,
}

/// The randomness used to apply zero-knowledge to commitment and accumulation.
/// If used, the randomness is the  [`Proof`][proof] of the
/// [`AtomicASForInnerProductArgPC`][as_for_ipa_pc].
///
/// [Proof]: crate::AccumulationScheme::Proof
/// [as_for_ipa_pc]: crate::ipa_pc_as::AtomicASForInnerProductArgPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Randomness<G: AffineCurve> {
    /// A random linear polynomial to be accumulated
    pub(crate) random_linear_polynomial: DensePolynomial<G::ScalarField>,

    /// The IpaPC commitment to the random linear polynomial.
    pub(crate) random_linear_polynomial_commitment: G,

    /// Randomness used to commit to the linear combination of the input polynomials.
    pub(crate) commitment_randomness: G::ScalarField,
}

/// The domain for the IpaPC sponge. Used as a substitution for forking for backwards compatibility.
pub struct IpaPCDomain {}
impl DomainSeparator for IpaPCDomain {
    fn domain() -> Vec<u8> {
        b"IPA-PC-2020".to_vec()
    }
}

/// The domain for the ASForIpaPC sponge. Used as a substitution for forking for backwards
/// compatibility.
pub struct ASForIpaPCDomain {}
impl DomainSeparator for ASForIpaPCDomain {
    fn domain() -> Vec<u8> {
        b"AS-FOR-IPA-PC-2020".to_vec()
    }
}

/// The current implementation of IpaPC requires passing in a sponge type as a generic type.
/// However, functions that IpaPC offer may not require the use of a sponge. This struct allows us
/// to always pass in a sponge as a generic type when the accumulation scheme API does not have
/// access to any sponge types (ie. in the indexer). Once IpaPC supports passing in sponge objects
/// only when necessary, we can remove this workaround.
#[derive(Clone)]
pub(crate) struct UnimplementedSponge {}
impl<CF: PrimeField> CryptographicSponge<CF> for UnimplementedSponge {
    fn new() -> Self {
        unimplemented!()
    }

    fn absorb(&mut self, _input: &impl Absorbable<CF>) {
        unimplemented!()
    }

    fn squeeze_bytes(&mut self, _num_bytes: usize) -> Vec<u8> {
        unimplemented!()
    }

    fn squeeze_bits(&mut self, _num_bits: usize) -> Vec<bool> {
        unimplemented!()
    }

    fn squeeze_field_elements(&mut self, _num_elements: usize) -> Vec<CF> {
        unimplemented!()
    }
}
