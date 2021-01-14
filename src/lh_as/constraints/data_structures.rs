use crate::lh_as::{InputInstance, SingleProof};
use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField, ToConstraintField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
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

pub struct VerifierKeyVar<CF: PrimeField>(pub(crate) FpVar<CF>);

impl<CF> AllocVar<Vec<u8>, CF> for VerifierKeyVar<CF>
where
    CF: PrimeField,
{
    fn new_variable<T: Borrow<Vec<u8>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let vk = f()?;
        let mut vk_cf: CF = vk.borrow().to_field_elements().unwrap().pop().unwrap();
        let vk_var = FpVar::<CF>::new_variable(ns.clone(), || Ok(vk_cf), mode)?;
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
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>
        + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge_var: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        sponge_var.absorb(self.commitment_var.to_constraint_field()?.as_slice())?;
        sponge_var.absorb(self.point_var.to_bytes()?.to_constraint_field()?.as_slice())?;
        sponge_var.absorb(self.eval_var.to_bytes()?.to_constraint_field()?.as_slice())
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
