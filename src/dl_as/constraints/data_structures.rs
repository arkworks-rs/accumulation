#![allow(unused)]
use crate::constraints::{ConstraintF, NNFieldVar};
use crate::dl_as::data_structures::{
    InputInstance, IsSpongeForAccSchemeParam, Randomness, SpongeForAccSchemeParam,
    SpongeForPCParam, VerifierKey,
};
use ark_ec::AffineCurve;
use ark_ff::Zero;
use ark_ff::{BitIteratorLE, Field, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly_commit::ipa_pc;
use ark_poly_commit::ipa_pc::SuccinctVerifierKey;
use ark_poly_commit::UVPolynomial;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::FieldElementSize;
use std::borrow::Borrow;
use std::marker::PhantomData;

pub type FinalCommKeyVar<C> = C;

pub struct VerifierKeyVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub(crate) ipa_vk: ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
    pub(crate) ipa_ck_linear: ipa_pc::constraints::VerifierKeyVar<G, C>,
}

impl<G, C> AllocVar<VerifierKey<G>, ConstraintF<G>> for VerifierKeyVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<VerifierKey<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|verifier_key| {
            let succinct_verifier_key = SuccinctVerifierKey::from_vk(&verifier_key.borrow().ipa_vk);
            let ipa_vk = ipa_pc::constraints::SuccinctVerifierKeyVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(succinct_verifier_key),
                mode,
            )?;

            let ipa_ck_linear = ipa_pc::constraints::VerifierKeyVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(&verifier_key.borrow().ipa_ck_linear),
                mode,
            )?;

            Ok(Self {
                ipa_vk,
                ipa_ck_linear,
            })
        })
    }
}

pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub(crate) ipa_commitment: ipa_pc::constraints::CommitmentVar<G, C>,
    pub(crate) point: NNFieldVar<G>,
    pub(crate) evaluation: NNFieldVar<G>,
    pub(crate) ipa_proof: ipa_pc::constraints::ProofVar<G, C>,
}

impl<G, C> AllocVar<InputInstance<G>, ConstraintF<G>> for InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<InputInstance<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|input_instance| {
            let ipa_commitment = ipa_pc::constraints::CommitmentVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().ipa_commitment),
                mode,
            )?;

            let point = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().point),
                mode,
            )?;

            let evaluation = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().evaluation),
                mode,
            )?;

            let ipa_proof = ipa_pc::constraints::ProofVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().ipa_proof),
                mode,
            )?;

            Ok(Self {
                ipa_commitment,
                point,
                evaluation,
                ipa_proof,
            })
        })
    }
}

pub struct RandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub(crate) random_linear_polynomial_coeffs: [NNFieldVar<G>; 2],
    pub(crate) random_linear_polynomial_commitment: C,
    pub(crate) commitment_randomness: Vec<Boolean<ConstraintF<G>>>,
}

impl<G, C> AllocVar<Randomness<G>, ConstraintF<G>> for RandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<Randomness<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let random_linear_polynomial_coeffs = &proof.borrow().random_linear_polynomial.coeffs();
            assert!(random_linear_polynomial_coeffs.len() <= 2);

            let random_linear_polynomial_coeffs = [
                NNFieldVar::<G>::new_variable(
                    ns.clone(),
                    || {
                        Ok(if random_linear_polynomial_coeffs.len() > 0 {
                            random_linear_polynomial_coeffs[0].clone()
                        } else {
                            G::ScalarField::zero()
                        })
                    },
                    mode,
                )?,
                NNFieldVar::<G>::new_variable(
                    ns.clone(),
                    || {
                        Ok(if random_linear_polynomial_coeffs.len() > 1 {
                            random_linear_polynomial_coeffs[1].clone()
                        } else {
                            G::ScalarField::zero()
                        })
                    },
                    mode,
                )?,
            ];

            let random_linear_polynomial_commitment = C::new_variable(
                ns.clone(),
                || Ok(proof.borrow().random_linear_polynomial_commitment),
                mode,
            )?;

            let commitment_randomness = BitIteratorLE::without_trailing_zeros(
                (&proof.borrow().commitment_randomness).into_repr(),
            )
            .map(|b| Boolean::new_variable(ns.clone(), || Ok(b), mode))
            .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                random_linear_polynomial_coeffs,
                random_linear_polynomial_commitment,
                commitment_randomness,
            })
        })
    }
}

pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub randomness: Option<RandomnessVar<G, C>>,
}

impl<G, C> AllocVar<Option<Randomness<G>>, ConstraintF<G>> for ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<Option<Randomness<G>>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let randomness = proof
                .borrow()
                .as_ref()
                .map(|rand| RandomnessVar::new_variable(ns.clone(), || Ok(rand.clone()), mode))
                .transpose()?;
            Ok(Self { randomness })
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone)]
pub struct DomainSeparatedSpongeVar<
    G: AffineCurve,
    S: CryptographicSpongeVar<ConstraintF<G>>,
    I: IsSpongeForAccSchemeParam,
> {
    sponge: S,
    absorbed_bit: bool,

    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
    _param: PhantomData<I>,
}

impl<G: AffineCurve, S: CryptographicSpongeVar<ConstraintF<G>>, I: IsSpongeForAccSchemeParam>
    DomainSeparatedSpongeVar<G, S, I>
{
    fn try_absorb_domain_bit(&mut self) -> Result<(), SynthesisError> {
        if !self.absorbed_bit {
            let is_for_sponge = if I::is_sponge_for_acc_scheme() {
                FpVar::one()
            } else {
                FpVar::zero()
            };

            self.sponge.absorb(&[is_for_sponge])?;

            self.absorbed_bit = true;
        }

        Ok(())
    }
}

impl<G: AffineCurve, S: CryptographicSpongeVar<ConstraintF<G>>, I: IsSpongeForAccSchemeParam>
    CryptographicSpongeVar<ConstraintF<G>> for DomainSeparatedSpongeVar<G, S, I>
{
    fn new(cs: ConstraintSystemRef<ConstraintF<G>>) -> Self {
        Self {
            sponge: S::new(cs),
            absorbed_bit: false,
            _affine: PhantomData,
            _sponge: PhantomData,
            _param: PhantomData,
        }
    }

    fn cs(&self) -> ConstraintSystemRef<ConstraintF<G>> {
        self.sponge.cs()
    }

    fn absorb(&mut self, input: &[FpVar<ConstraintF<G>>]) -> Result<(), SynthesisError> {
        self.try_absorb_domain_bit()?;
        self.sponge.absorb(input)
    }

    fn squeeze_bytes(
        &mut self,
        num_bytes: usize,
    ) -> Result<Vec<UInt8<ConstraintF<G>>>, SynthesisError> {
        self.try_absorb_domain_bit()?;
        self.sponge.squeeze_bytes(num_bytes)
    }

    fn squeeze_bits(
        &mut self,
        num_bits: usize,
    ) -> Result<Vec<Boolean<ConstraintF<G>>>, SynthesisError> {
        self.try_absorb_domain_bit()?;
        self.sponge.squeeze_bits(num_bits)
    }

    fn squeeze_field_elements(
        &mut self,
        num_elements: usize,
    ) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        self.try_absorb_domain_bit()?;
        self.sponge.squeeze_field_elements(num_elements)
    }

    fn squeeze_nonnative_field_elements_with_sizes<F: PrimeField>(
        &mut self,
        sizes: &[FieldElementSize],
    ) -> Result<
        (
            Vec<NonNativeFieldVar<F, ConstraintF<G>>>,
            Vec<Vec<Boolean<ConstraintF<G>>>>,
        ),
        SynthesisError,
    > {
        self.try_absorb_domain_bit()?;
        self.sponge
            .squeeze_nonnative_field_elements_with_sizes(sizes)
    }
}

pub type SpongeVarForAccScheme<G, S> = DomainSeparatedSpongeVar<G, S, SpongeForAccSchemeParam>;
pub type SpongeVarForPC<G, S> = DomainSeparatedSpongeVar<G, S, SpongeForPCParam>;
