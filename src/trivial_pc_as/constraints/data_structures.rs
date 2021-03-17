use crate::constraints::NNFieldVar;
use crate::trivial_pc_as::{InputInstance, SingleProof};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::{collect_sponge_field_elements_gadget, Absorbable};
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;
use ark_std::vec::Vec;

/// The [`VerifierKey`][vk] of the [`TrivialPcASVerifierGadget`][trivial_pc_as_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [trivial_pc_as_verifier]: crate::trivial_pc_as::constraints::TrivialPcASVerifierGadget
pub struct VerifierKeyVar<CF: PrimeField>(pub(crate) FpVar<CF>);

impl<CF> AllocVar<usize, CF> for VerifierKeyVar<CF>
where
    CF: PrimeField,
{
    fn new_variable<T: Borrow<usize>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            let vk = FpVar::<CF>::new_variable(
                ns.clone(),
                || {
                    Ok(Absorbable::<CF>::to_sponge_field_elements(vk.borrow())
                        .pop()
                        .unwrap())
                },
                mode,
            )?;
            Ok(VerifierKeyVar(vk))
        })
    }
}

/// The [`InputInstance`][input] of the [`TrivialPcASVerifierGadget`][trivial_pc_as_verifier].
///
/// [input]: crate::constraints::ASVerifierGadget::InputInstance
/// [trivial_pc_as_verifier]: crate::trivial_pc_as::constraints::TrivialPcASVerifierGadget
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// Pedersen commitment to a polynomial.
    pub commitment: C,

    /// Point where the proof was opened at.
    pub point: NNFieldVar<G>,

    /// Evaluation of the committed polynomial at the point.
    pub eval: NNFieldVar<G>,

    #[doc(hidden)]
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
            let pedersen_comm: G = input_instance.borrow().commitment.commitment().elem;
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

impl<G, C> AbsorbableGadget<ConstraintF<G>> for InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(
            self.commitment,
            self.point.to_bytes()?,
            self.eval.to_bytes()?
        )
    }
}

/// A proof attesting that a single input was properly accumulated.
pub struct SingleProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// Pedersen commitment to the witness polynomial.
    pub(crate) witness_commitment: C,

    /// Evaluation of the witness polynomial at the challenge point.
    pub(crate) witness_eval: NNFieldVar<G>,

    /// Evaluation of the input polynomial at the challenge point.
    pub(crate) eval: NNFieldVar<G>,

    #[doc(hidden)]
    pub(crate) _affine: PhantomData<G>,
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
            let witness_commitment: G = single_proof.borrow().witness_commitment.commitment().elem;
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

/// The [`Proof`][proof] of the [`TrivialPcASVerifierGadget`][trivial_pc_as_verifier].
///
/// [proof]: crate::constraints::ASVerifierGadget::Proof
/// [trivial_pc_as_verifier]: crate::trivial_pc_as::constraints::TrivialPcASVerifierGadget
pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
{
    /// A list of [`SingleProofVar`] for each input.
    pub(crate) single_proofs: Vec<SingleProofVar<G, C>>,
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
