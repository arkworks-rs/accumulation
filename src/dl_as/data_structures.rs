use crate::std::vec::Vec;
use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_poly_commit::{ipa_pc, LabeledCommitment, UVPolynomial};
use ark_sponge::{Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(Clone)]
pub struct PredicateIndex {
    pub(crate) supported_degree_bound: usize,
    pub(crate) supported_hiding_bound: usize,
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct InputInstance<G: AffineCurve> {
    // ipa_pc instance
    pub(crate) ipa_commitment: LabeledCommitment<ipa_pc::Commitment<G>>,
    pub(crate) point: G::ScalarField,
    pub(crate) evaluation: G::ScalarField,

    // ipa_pc proof
    pub(crate) ipa_proof: ipa_pc::Proof<G>,
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct Proof<G: AffineCurve, P: UVPolynomial<G::ScalarField>> {
    pub(crate) random_linear_polynomial: P,
    pub(crate) random_linear_polynomial_commitment: G,
    pub(crate) commitment_randomness: G::ScalarField,
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct ProverKey<G: AffineCurve> {
    pub(crate) ipa_ck: ipa_pc::CommitterKey<G>,
    pub(crate) verifier_key: VerifierKey<G>,
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct VerifierKey<G: AffineCurve> {
    pub(crate) ipa_vk: ipa_pc::VerifierKey<G>,
    pub(crate) ipa_ck_linear: ipa_pc::CommitterKey<G>,
}

#[derive(Derivative)]
#[derivative(Clone)]
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
    F: PrimeField,
    S: CryptographicSponge<F>,
    I: IsSpongeForAccSchemeParam,
> {
    sponge: S,
    _field: PhantomData<F>,
    _param: PhantomData<I>,
}

impl<F: PrimeField, S: CryptographicSponge<F>, I: IsSpongeForAccSchemeParam> CryptographicSponge<F>
    for DomainSeparatedSponge<F, S, I>
{
    fn new() -> Self {
        let mut sponge = S::new();
        sponge.absorb(&I::is_sponge_for_acc_scheme());
        Self {
            sponge,
            _field: PhantomData,
            _param: PhantomData,
        }
    }

    fn absorb(&mut self, input: &impl Absorbable<F>) {
        self.sponge.absorb(input);
    }

    fn squeeze_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        self.sponge.squeeze_bytes(num_bytes)
    }

    fn squeeze_field_elements_with_sizes(&mut self, sizes: &[FieldElementSize]) -> Vec<F> {
        self.sponge.squeeze_field_elements_with_sizes(sizes)
    }
}

pub type SpongeForAccScheme<F, S> = DomainSeparatedSponge<F, S, SpongeForAccSchemeParam>;
pub type SpongeForPC<F, S> = DomainSeparatedSponge<F, S, SpongeForPCParam>;
