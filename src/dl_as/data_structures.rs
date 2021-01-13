use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_poly_commit::{ipa_pc, LabeledCommitment, UVPolynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::io::{Read, Write};
use ark_std::marker::PhantomData;

#[derive(Clone)]
pub struct PredicateIndex {
    pub supported_degree_bound: usize,
    pub supported_hiding_bound: usize,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<G: AffineCurve> {
    // ipa_pc instance
    pub ipa_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,
    pub point: G::ScalarField,
    pub evaluation: G::ScalarField,

    // ipa_pc proof
    pub ipa_proof: ipa_pc::Proof<G>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve, P: UVPolynomial<G::ScalarField>> {
    // TODO: Replace with size two tuple or array of coeffs to enforce linear polynomial?
    pub(crate) random_linear_polynomial: P,
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

#[derive(Clone)]
pub struct DeciderKey<G: AffineCurve>(pub(crate) ipa_pc::VerifierKey<G>);

pub trait IsSpongeForAccSchemeParam {
    fn is_sponge_for_acc_scheme() -> bool;
}

pub struct SpongeForAccSchemeParam {}
impl IsSpongeForAccSchemeParam for SpongeForAccSchemeParam {
    fn is_sponge_for_acc_scheme() -> bool {
        true
    }
}

pub struct SpongeForPCParam {}
impl IsSpongeForAccSchemeParam for SpongeForPCParam {
    fn is_sponge_for_acc_scheme() -> bool {
        false
    }
}

pub struct DomainSeparatedSponge<
    CF: PrimeField + Absorbable<CF>,
    S: CryptographicSponge<CF>,
    I: IsSpongeForAccSchemeParam,
> {
    sponge: S,
    _field: PhantomData<CF>,
    _param: PhantomData<I>,
}

impl<CF: PrimeField + Absorbable<CF>, S: CryptographicSponge<CF>, I: IsSpongeForAccSchemeParam>
    CryptographicSponge<CF> for DomainSeparatedSponge<CF, S, I>
{
    fn new() -> Self {
        let mut sponge = S::new();
        sponge.absorb(&if I::is_sponge_for_acc_scheme() {
            CF::one()
        } else {
            CF::zero()
        });
        Self {
            sponge,
            _field: PhantomData,
            _param: PhantomData,
        }
    }

    fn absorb(&mut self, input: &impl Absorbable<CF>) {
        self.sponge.absorb(input);
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        self.sponge.squeeze_bytes(num_bytes)
    }

    fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        self.sponge.squeeze_bits(num_bits)
    }

    fn squeeze_field_elements_with_sizes(&mut self, sizes: &[FieldElementSize]) -> Vec<CF> {
        self.sponge.squeeze_field_elements_with_sizes(sizes)
    }

    fn squeeze_field_elements(&mut self, num_elements: usize) -> Vec<CF> {
        self.sponge.squeeze_field_elements(num_elements)
    }

    fn squeeze_nonnative_field_elements_with_sizes<F: PrimeField>(
        &mut self,
        sizes: &[FieldElementSize],
    ) -> Vec<F> {
        self.sponge
            .squeeze_nonnative_field_elements_with_sizes(sizes)
    }

    fn squeeze_nonnative_field_elements<F: PrimeField>(&mut self, num_elements: usize) -> Vec<F> {
        self.sponge.squeeze_nonnative_field_elements(num_elements)
    }
}

pub type SpongeForAccScheme<F, S> = DomainSeparatedSponge<F, S, SpongeForAccSchemeParam>;
pub type SpongeForPC<F, S> = DomainSeparatedSponge<F, S, SpongeForPCParam>;
