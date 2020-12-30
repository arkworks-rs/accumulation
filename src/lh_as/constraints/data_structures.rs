use crate::lh_as::{InputInstance, SingleProof};
use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_marlin::fiat_shamir::constraints::FiatShamirRngVar;
use ark_marlin::fiat_shamir::FiatShamirRng;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use std::borrow::Borrow;
use std::marker::PhantomData;

pub(crate) type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
pub(crate) type NNFieldVar<G> = NonNativeFieldVar<
    <G as AffineCurve>::ScalarField,
    <<G as AffineCurve>::BaseField as Field>::BasePrimeField,
>;

pub struct VerifierKeyVar<G: AffineCurve>(pub(crate) NNFieldVar<G>);
impl<G> AllocVar<G::ScalarField, ConstraintF<G>> for VerifierKeyVar<G>
where
    G: AffineCurve,
{
    fn new_variable<T: Borrow<G::ScalarField>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let vk = f()?;
        let vk_var = NNFieldVar::<G>::new_variable(ns.clone(), || Ok(vk.borrow().clone()), mode)?;
        Ok(VerifierKeyVar(vk_var))
    }
}

// Specialized for Pedersen commitments
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub commitment_var: C,
    pub point_var: NNFieldVar<G>,
    pub eval_var: NNFieldVar<G>,

    pub _affine: PhantomData<G>,
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
        let input_instance = f()?;
        let pedersen_comm: G = (input_instance.borrow().commitment.commitment().0)
            .0
            .clone();
        let commitment_var = C::new_variable(ns.clone(), || Ok(pedersen_comm), mode)?;
        let point_var = NNFieldVar::<G>::new_variable(
            ns.clone(),
            || Ok(input_instance.borrow().point.clone()),
            mode,
        )?;
        let eval_var = NNFieldVar::<G>::new_variable(
            ns.clone(),
            || Ok(input_instance.borrow().eval.clone()),
            mode,
        )?;

        Ok(Self {
            commitment_var,
            point_var,
            eval_var,
            _affine: PhantomData,
        })
    }
}

impl<G, C> InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub fn absorb_into_sponge<S, SV>(&self, sponge_var: &mut SV) -> Result<(), SynthesisError>
    where
        S: FiatShamirRng<G::ScalarField, ConstraintF<G>>,
        SV: FiatShamirRngVar<G::ScalarField, ConstraintF<G>, S>,
    {
        let mut byte_vars = self.commitment_var.to_bytes()?;
        byte_vars.extend(self.point_var.to_bytes()?);
        byte_vars.extend(self.eval_var.to_bytes()?);

        sponge_var.absorb_bytes(byte_vars.as_slice())
    }
}

pub struct SingleProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub witness_commitment_var: C,
    pub witness_eval_var: NNFieldVar<G>,
    pub eval_var: NNFieldVar<G>,

    pub _affine: PhantomData<G>,
}

impl<G, C> AllocVar<SingleProof<G>, ConstraintF<G>> for SingleProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<SingleProof<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let single_proof = f()?;
        let witness_commitment: G = (single_proof.borrow().witness_commitment.commitment().0)
            .0
            .clone();
        let witness_commitment_var = C::new_variable(ns.clone(), || Ok(witness_commitment), mode)?;
        let witness_eval_var = NNFieldVar::<G>::new_variable(
            ns.clone(),
            || Ok(single_proof.borrow().witness_eval.clone()),
            mode,
        )?;
        let eval_var = NNFieldVar::<G>::new_variable(
            ns.clone(),
            || Ok(single_proof.borrow().eval.clone()),
            mode,
        )?;

        Ok(Self {
            witness_commitment_var,
            witness_eval_var,
            eval_var,
            _affine: PhantomData,
        })
    }
}

pub type ProofVar<G, C> = Vec<SingleProofVar<G, C>>;
