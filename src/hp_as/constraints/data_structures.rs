use crate::constraints::ConstraintF;
use crate::hp_as::data_structures::{Proof, ProofHidingCommitments, ProofTCommitments};
use crate::hp_as::InputInstance;
use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::collect_sponge_field_elements_gadget;
use ark_sponge::constraints::absorbable::AbsorbableGadget;
use std::borrow::Borrow;
use std::marker::PhantomData;

/// The [`VerifierKey`][vk] of the [`HpASVerifierGadget`][hp_as_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [hp_as_verifier]: crate::hp_as::constraints::HpASVerifierGadget
pub struct VerifierKeyVar<CF: PrimeField> {
    /// Supported vector length of the Hadamard product relation.
    pub(crate) num_supported_elems: FpVar<CF>,
}

impl<CF: PrimeField> AllocVar<usize, CF> for VerifierKeyVar<CF> {
    fn new_variable<T: Borrow<usize>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            Ok(VerifierKeyVar {
                num_supported_elems: FpVar::new_variable(
                    ns.clone(),
                    || Ok(CF::from(*vk.borrow() as u64)),
                    mode,
                )?,
            })
        })
    }
}

/// The [`InputInstance`][input] of the [`HpASVerifierGadget`][hp_as_verifier].
///
/// [input]: crate::constraints::ASVerifierGadget::InputInstance
/// [hp_as_verifier]: crate::hp_as::constraints::HpASVerifierGadget
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Commitment to the `a` vector of the Hadamard product relation.
    pub comm_1: C,

    /// Commitment to the `b` vector of the Hadamard product relation.
    pub comm_2: C,

    /// Commitment to the `a ◦ b` vector of the Hadamard product relation.
    pub comm_3: C,

    #[doc(hidden)]
    pub _curve: PhantomData<G>,
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
            let comm_1 = C::new_variable(ns.clone(), || Ok(input_instance.borrow().comm_1), mode)?;
            let comm_2 = C::new_variable(ns.clone(), || Ok(input_instance.borrow().comm_2), mode)?;
            let comm_3 = C::new_variable(ns.clone(), || Ok(input_instance.borrow().comm_3), mode)?;
            Ok(Self {
                comm_1,
                comm_2,
                comm_3,
                _curve: PhantomData,
            })
        })
    }
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.comm_1, self.comm_2, self.comm_3)
    }
}

/// The [`Proof`][proof] of the [`HpASVerifierGadget`][hp_as_verifier].
///
/// [proof]: crate::constraints::ASVerifierGadget::Proof
/// [hp_as_verifier]: crate::hp_as::constraints::HpASVerifierGadget
pub struct ProofVar<G, C>
    where
        G: AffineCurve,
        C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
    /// Excludes `n-1`th commitment (0-index)
    pub(crate) t_comms: ProofTCommitmentsVar<G, C>,

    /// Commitments to the random vectors used to apply zero-knowledge to the vectors of the
    /// Hadamard product relation.
    pub(crate) hiding_comms: Option<ProofHidingCommitmentsVar<G, C>>,

    #[doc(hidden)]
    pub(crate) _curve: PhantomData<G>,
}

impl<G, C> AllocVar<Proof<G>, ConstraintF<G>> for ProofVar<G, C>
    where
        G: AffineCurve,
        C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<Proof<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let t_comms = ProofTCommitmentsVar::new_variable(
                ns.clone(),
                || Ok(&proof.borrow().t_comms),
                mode,
            )?;
            let hiding_comms = proof
                .borrow()
                .hiding_comms
                .as_ref()
                .map(|hiding_comms| {
                    ProofHidingCommitmentsVar::new_variable(ns.clone(), || Ok(hiding_comms), mode)
                })
                .transpose()?;

            Ok(Self {
                t_comms,
                hiding_comms,
                _curve: PhantomData,
            })
        })
    }
}

/// The commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
/// Excludes `n-1`th commitment (0-index)
pub(crate) struct ProofTCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// The first `n-1` commitments.
    pub(crate) low: Vec<C>,

    /// The last `n-1` commitments.
    pub(crate) high: Vec<C>,

    #[doc(hidden)]
    pub(crate) _curve: PhantomData<G>,
}

impl<G, C> AllocVar<ProofTCommitments<G>, ConstraintF<G>> for ProofTCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<ProofTCommitments<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|t_comms| {
            let t_comms_low = t_comms
                .borrow()
                .low
                .iter()
                .map(|t_comm| C::new_variable(ns.clone(), || Ok(t_comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let t_comms_high = t_comms
                .borrow()
                .high
                .iter()
                .map(|t_comm| C::new_variable(ns.clone(), || Ok(t_comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                low: t_comms_low,
                high: t_comms_high,
                _curve: PhantomData,
            })
        })
    }
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for ProofTCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.low, self.high)
    }
}

/// The commitments to the random vectors used to apply zero-knowledge to the vectors of the
/// Hadamard product relation.
pub(crate) struct ProofHidingCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Commitment to the random vector that hides the `a` vector of the Hadamard product relation.
    pub(crate) comm_1: C,

    /// Commitment to the random vector that hides the `b` vector of the Hadamard product relation.
    pub(crate) comm_2: C,

    /// Commitment to the vector that applies the random vectors to the product polynomial
    /// `a(ν, µ) ◦ b(ν)`.
    pub(crate) comm_3: C,

    #[doc(hidden)]
    pub(crate) _curve: PhantomData<G>,
}

impl<G, C> AllocVar<ProofHidingCommitments<G>, ConstraintF<G>> for ProofHidingCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<ProofHidingCommitments<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|hiding_comms| {
            let comm_1 = C::new_variable(ns.clone(), || Ok(hiding_comms.borrow().comm_1), mode)?;
            let comm_2 = C::new_variable(ns.clone(), || Ok(hiding_comms.borrow().comm_2), mode)?;
            let comm_3 = C::new_variable(ns.clone(), || Ok(hiding_comms.borrow().comm_3), mode)?;

            Ok(Self {
                comm_1,
                comm_2,
                comm_3,
                _curve: PhantomData,
            })
        })
    }
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for ProofHidingCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.comm_1, self.comm_2, self.comm_3)
    }
}

