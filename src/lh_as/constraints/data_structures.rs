use crate::constraints::{ConstraintF, NNFieldVar};
use crate::lh_as::{InputInstance, SingleProof};
use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;
use std::borrow::Borrow;
use std::marker::PhantomData;

pub struct VerifierKeyVar<CF: PrimeField>(pub(crate) FpVar<CF>);

impl<CF> AllocVar<CF, CF> for VerifierKeyVar<CF>
where
    CF: PrimeField,
{
    fn new_variable<T: Borrow<CF>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            let vk = FpVar::<CF>::new_variable(ns.clone(), || Ok(vk.borrow().clone()), mode)?;
            Ok(VerifierKeyVar(vk))
        })
    }
}

// Specialized for Pedersen commitments
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub commitment: C,
    pub point: NNFieldVar<G>,
    pub eval: NNFieldVar<G>,

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
        f().and_then(|input_instance| {
            let pedersen_comm: G = (input_instance.borrow().commitment.commitment().0)
                .0
                .clone();
            let commitment = C::new_variable(ns.clone(), || Ok(pedersen_comm), mode)?;
            let point = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().point),
                mode,
            )?;
            let eval = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&input_instance.borrow().eval),
                mode,
            )?;

            Ok(Self {
                commitment,
                point,
                eval,
                _affine: PhantomData,
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
    pub fn absorb_into_sponge<S, SV>(&self, sponge: &mut SV) -> Result<(), SynthesisError>
    where
        S: CryptographicSponge<ConstraintF<G>>,
        SV: CryptographicSpongeVar<ConstraintF<G>, S>,
    {
        sponge.absorb(self.commitment.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.point.to_bytes()?.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.eval.to_bytes()?.to_constraint_field()?.as_slice())
    }
}

pub struct SingleProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub witness_commitment: C,
    pub witness_eval: NNFieldVar<G>,
    pub eval: NNFieldVar<G>,

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
        f().and_then(|single_proof| {
            let witness_commitment: G = (single_proof.borrow().witness_commitment.commitment().0)
                .0
                .clone();
            let witness_commitment = C::new_variable(ns.clone(), || Ok(witness_commitment), mode)?;
            let witness_eval = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&single_proof.borrow().witness_eval),
                mode,
            )?;
            let eval = NNFieldVar::<G>::new_variable(
                ns.clone(),
                || Ok(&single_proof.borrow().eval),
                mode,
            )?;

            Ok(Self {
                witness_commitment,
                witness_eval,
                eval,
                _affine: PhantomData,
            })
        })
    }
}

pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    pub single_proofs: Vec<SingleProofVar<G, C>>,
}

impl<G, C> AllocVar<Vec<SingleProof<G>>, ConstraintF<G>> for ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<Vec<SingleProof<G>>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|single_proofs| {
            let single_proof_vars = single_proofs
                .borrow()
                .into_iter()
                .map(|single_proof| {
                    SingleProofVar::new_variable(ns.clone(), || Ok(single_proof.clone()), mode)
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                single_proofs: single_proof_vars,
            })
        })
    }
}
