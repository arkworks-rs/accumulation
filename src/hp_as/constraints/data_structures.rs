use crate::constraints::ConstraintF;
use crate::hp_as::data_structures::{Proof, ProofHidingCommitments, ProofTCommitments};
use crate::hp_as::InputInstance;
use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::absorbable::AbsorbableGadget;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{collect_sponge_field_elements_gadget, CryptographicSponge};
use std::borrow::Borrow;
use std::marker::PhantomData;

/// Represents the verifier key that is used when accumulating instances and old accumulators.
pub struct VerifierKeyVar<CF: PrimeField> {
    pub num_supported_elems: FpVar<CF>,
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

/// Represents an accumulatable instance of the Hadamard product relation.
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    pub comm_1: C,
    pub comm_2: C,
    pub comm_3: C,
    pub(crate) _curve: PhantomData<G>,
}

pub type AccumulatorInstanceVar<G, C> = InputInstanceVar<G, C>;

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

pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    pub t_comms: ProofTCommitmentsVar<G, C>,
    pub hiding_comms: Option<ProofHidingCommitmentsVar<G, C>>,
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

pub struct ProofTCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    pub low: Vec<C>,
    pub high: Vec<C>,
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

pub struct ProofHidingCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    pub comm_1: C,
    pub comm_2: C,
    pub comm_3: C,
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
