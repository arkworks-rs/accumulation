use crate::hp_as::data_structures::Proof;
use crate::hp_as::InputInstance;
use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField, ToConstraintField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{R1CSVar, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use std::borrow::Borrow;
use std::marker::PhantomData;

pub(crate) type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
pub(crate) type NNFieldVar<G> = NonNativeFieldVar<
    <G as AffineCurve>::ScalarField,
    <<G as AffineCurve>::BaseField as Field>::BasePrimeField,
>;

/// Represents the verifier key that is used when accumulating instances and old accumulators.
pub struct VerifierKeyVar;

impl<CF: PrimeField> AllocVar<(), CF> for VerifierKeyVar {
    fn new_variable<T: Borrow<()>>(
        _cs: impl Into<Namespace<CF>>,
        _f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Ok(VerifierKeyVar)
    }
}

/// Represents an accumulatable instance of the Hadamard product relation.
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
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

impl<G, C> InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        sponge.absorb(&self.comm_1.to_constraint_field()?)?;
        sponge.absorb(&self.comm_2.to_constraint_field()?)?;
        sponge.absorb(&self.comm_3.to_constraint_field()?)?;
        Ok(())
    }
}

pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub t_comms: (Vec<C>, Vec<C>),
    pub(crate) _curve: PhantomData<G>,
}

impl<G, C> ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        for t_0 in &self.t_comms.0 {
            sponge.absorb(&t_0.to_constraint_field()?)?;
        }

        for t_1 in &self.t_comms.1 {
            sponge.absorb(&t_1.to_constraint_field()?)?;
        }
        Ok(())
    }
}

impl<G, C> AllocVar<Proof<G>, ConstraintF<G>> for ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
{
    fn new_variable<T: Borrow<Proof<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|proof| {
            let t_comms_low = proof
                .borrow()
                .t_comms
                .0
                .iter()
                .map(|t_comm| C::new_variable(ns.clone(), || Ok(t_comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let t_comms_high = proof
                .borrow()
                .t_comms
                .1
                .iter()
                .map(|t_comm| C::new_variable(ns.clone(), || Ok(t_comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                t_comms: (t_comms_low, t_comms_high),
                _curve: PhantomData,
            })
        })
    }
}
