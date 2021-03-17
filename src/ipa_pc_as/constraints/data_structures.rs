use crate::constraints::NNFieldVar;
use crate::ipa_pc_as::data_structures::{InputInstance, Randomness, VerifierKey};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::Zero;
use ark_ff::{BitIteratorLE, Field, PrimeField};
use ark_poly_commit::ipa_pc;
use ark_poly_commit::UVPolynomial;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;
use ark_std::vec::Vec;

pub(crate) type FinalCommKeyVar<C> = C;

/// The [`VerifierKey`][vk] of the [`IpaPCAtomicASVerifierGadget`][ipa_pc_as_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [ipa_pc_as_verifier]: crate::ipa_pc_as::constraints::IpaPCAtomicASVerifierGadget
pub struct VerifierKeyVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub(crate) ipa_svk: ipa_pc::constraints::SuccinctVerifierKeyVar<G, C>,
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
            let ipa_svk = ipa_pc::constraints::SuccinctVerifierKeyVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(verifier_key.borrow().ipa_svk.clone()),
                mode,
            )?;

            let ipa_ck_linear = ipa_pc::constraints::VerifierKeyVar::<G, C>::new_variable(
                ns.clone(),
                || Ok(&verifier_key.borrow().ipa_ck_linear),
                mode,
            )?;

            Ok(Self {
                ipa_svk,
                ipa_ck_linear,
            })
        })
    }
}

/// The [`InputInstance`][input_instance] of the
/// [`IpaPCAtomicASVerifierGadget`][ipa_pc_as_verifier].
///
/// [input_instance]: crate::constraints::ASVerifierGadget::InputInstance
/// [ipa_pc_as_verifier]: crate::ipa_pc_as::constraints::IpaPCAtomicASVerifierGadget
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// The IpaPC commitment to a polynomial.
    pub(crate) ipa_commitment: ipa_pc::constraints::CommitmentVar<G, C>,

    /// Point where the proof was opened at.
    pub(crate) point: NNFieldVar<G>,

    /// Evaluation of the committed polynomial at the point.
    pub(crate) evaluation: NNFieldVar<G>,

    /// The IpaPC proof of evaluation at the point.
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

/// The randomness used to apply zero-knowledge to commitment and accumulation.
pub struct RandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// A random linear polynomial to be accumulated.
    pub(crate) random_linear_polynomial_coeffs: [NNFieldVar<G>; 2],

    /// The IpaPC commitment to the random linear polynomial.
    pub(crate) random_linear_polynomial_commitment: C,

    /// Randomness used to commit to the linear combination of the input polynomials.
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

/// The [`Proof`][proof] of the [`IpaPCAtomicASVerifierGadget`][ipa_pc_as_verifier].
///
/// [proof]: crate::constraints::ASVerifierGadget::Proof
/// [ipa_pc_as_verifier]: crate::ipa_pc_as::constraints::IpaPCAtomicASVerifierGadget
pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// Randomness used to apply zero-knowledge to commitment and accumulation.
    pub(crate) randomness: Option<RandomnessVar<G, C>>,
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
