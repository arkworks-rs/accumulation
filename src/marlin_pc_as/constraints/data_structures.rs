use crate::marlin_pc_as::{AccumulatorInstance, InputInstance, MarlinPCInstance, Randomness};

use ark_ec::PairingEngine;
use ark_ff::{BitIteratorLE, PrimeField};
use ark_poly_commit::marlin_pc;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::uint8::UInt8;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::collect_sponge_field_elements_gadget;
use ark_sponge::constraints::AbsorbableGadget;
use ark_std::borrow::Borrow;

/// An instance of the MarlinPC relation.
pub struct MarlinPCInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    /// The MarlinPC commitment to a polynomial.
    pub(crate) commitment: marlin_pc::LabeledCommitmentVar<E, PV>,

    /// Point where the proof was opened at.
    pub(crate) point: Vec<Boolean<E::Fq>>,

    /// Evaluation of the committed polynomial at the point.
    pub(crate) evaluation: Vec<Boolean<E::Fq>>,
}

impl<E, PV> AllocVar<MarlinPCInstance<E>, E::Fq> for MarlinPCInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn new_variable<T: Borrow<MarlinPCInstance<E>>>(
        cs: impl Into<Namespace<<E as PairingEngine>::Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|instance| {
            let instance = instance.borrow();

            let commitment = marlin_pc::LabeledCommitmentVar::new_variable(
                ns.clone(),
                || Ok(instance.commitment.clone()),
                mode,
            )?;

            let point = BitIteratorLE::new((&instance.point).into_repr())
                .map(|b| Boolean::new_variable(ns.clone(), || Ok(b), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let evaluation = BitIteratorLE::new((&instance.evaluation).into_repr())
                .map(|b| Boolean::new_variable(ns.clone(), || Ok(b), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                commitment,
                point,
                evaluation,
            })
        })
    }
}

impl<E, PV> AbsorbableGadget<E::Fq> for MarlinPCInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
{
    fn to_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<<E as PairingEngine>::Fq>>, SynthesisError> {
        let point_bytes = self
            .point
            .chunks(8)
            .map(|c| {
                if c.len() == 8 {
                    UInt8::<E::Fq>::from_bits_le(c)
                } else {
                    let mut resized = c.to_vec();
                    resized.resize_with(8, || Boolean::FALSE);
                    UInt8::<E::Fq>::from_bits_le(&resized)
                }
            })
            .collect::<Vec<_>>();

        let evaluation_bytes = self
            .evaluation
            .chunks(8)
            .map(|c| {
                if c.len() == 8 {
                    UInt8::<E::Fq>::from_bits_le(c)
                } else {
                    let mut resized = c.to_vec();
                    resized.resize_with(8, || Boolean::FALSE);
                    UInt8::<E::Fq>::from_bits_le(&resized)
                }
            })
            .collect::<Vec<_>>();

        let degree_bound = self
            .commitment
            .degree_bound
            .as_ref()
            .map(|d| d.to_bytes())
            .transpose()?;

        collect_sponge_field_elements_gadget!(
            self.commitment.commitment,
            degree_bound,
            point_bytes,
            evaluation_bytes
        )
    }
}

/// The [`InputInstance`][input_instance] of the
/// [`AtomicASForMarlinPCVerifierGadget`][as_for_marlin_pc_verifier].
///
/// [input_instance]: crate::constraints::ASVerifierGadget::InputInstance
/// [as_for_marlin_pc_verifier]: crate::marlin_pc_as::constraints::AtomicASForMarlinPCVerifierGadget
pub struct InputInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    /// The MarlinPC instance.
    pub marlin_pc_instance: MarlinPCInstanceVar<E, PV>,

    /// The MarlinPC proof.
    pub marlin_pc_proof: marlin_pc::ProofVar<E, PV>,
}

impl<E, PV> AllocVar<InputInstance<E>, E::Fq> for InputInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn new_variable<T: Borrow<InputInstance<E>>>(
        cs: impl Into<Namespace<<E as PairingEngine>::Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|instance| {
            let instance = instance.borrow();

            let marlin_pc_instance = MarlinPCInstanceVar::new_variable(
                ns.clone(),
                || Ok(instance.marlin_pc_instance.clone()),
                mode,
            )?;

            let marlin_pc_proof = marlin_pc::ProofVar::new_variable(
                ns.clone(),
                || Ok(instance.marlin_pc_proof.clone()),
                mode,
            )?;

            Ok(Self {
                marlin_pc_instance,
                marlin_pc_proof,
            })
        })
    }
}

impl<E, PV> AbsorbableGadget<E::Fq> for InputInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
{
    fn to_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<<E as PairingEngine>::Fq>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.marlin_pc_instance, self.marlin_pc_proof)
    }
}

/// The [`AccumulatorInstance`][acc_instance] of the
/// [`AtomicASForMarlinPCVerifierGadget`][as_for_marlin_pc_verifier].
///
/// [acc_instance]: crate::constraints::ASVerifierGadget::AccumulatorInstance
/// [as_for_marlin_pc_verifier]: crate::marlin_pc_as::constraints::AtomicASForMarlinPCVerifierGadget
pub struct AccumulatorInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    /// The accumulated MarlinPC commitment.
    pub(crate) accumulated_commitment: PV::G1Var,

    /// The accumulated MarlinPC proof.
    pub(crate) accumulated_proof: PV::G1Var,
}

impl<E, PV> AllocVar<AccumulatorInstance<E>, E::Fq> for AccumulatorInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn new_variable<T: Borrow<AccumulatorInstance<E>>>(
        cs: impl Into<Namespace<<E as PairingEngine>::Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|instance| {
            let instance = instance.borrow();

            let accumulated_commitment = PV::G1Var::new_variable(
                ns.clone(),
                || Ok(instance.accumulated_commitment.clone()),
                mode,
            )?;

            let accumulated_proof = PV::G1Var::new_variable(
                ns.clone(),
                || Ok(instance.accumulated_proof.clone()),
                mode,
            )?;

            Ok(Self {
                accumulated_commitment,
                accumulated_proof,
            })
        })
    }
}

impl<E, PV> EqGadget<E::Fq> for AccumulatorInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<<E as PairingEngine>::Fq>, SynthesisError> {
        let commitment_is_eq = self
            .accumulated_commitment
            .is_eq(&other.accumulated_commitment)?;

        let proof_is_eq = self.accumulated_proof.is_eq(&other.accumulated_proof)?;

        Ok(commitment_is_eq.and(&proof_is_eq)?)
    }
}

impl<E, PV> AbsorbableGadget<E::Fq> for AccumulatorInstanceVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
{
    fn to_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<<E as PairingEngine>::Fq>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.accumulated_commitment, self.accumulated_proof)
    }
}

/// The randomness used to apply zero-knowledge to the accumulated commitment and proof.
pub struct RandomnessVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    /// The randomness used to blind the accumulated commitment.
    pub(crate) accumulated_commitment_randomness: PV::G1Var,

    /// The randomness used to blind the accumulated proof.
    pub(crate) accumulated_proof_randomness: PV::G1Var,
}

impl<E, PV> AllocVar<Randomness<E>, E::Fq> for RandomnessVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn new_variable<T: Borrow<Randomness<E>>>(
        cs: impl Into<Namespace<<E as PairingEngine>::Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|randomness| {
            let randomness = randomness.borrow();

            let accumulated_commitment_randomness = PV::G1Var::new_variable(
                ns.clone(),
                || Ok(randomness.accumulated_commitment_randomness.clone()),
                mode,
            )?;

            let accumulated_proof_randomness = PV::G1Var::new_variable(
                ns.clone(),
                || Ok(randomness.accumulated_proof_randomness.clone()),
                mode,
            )?;

            Ok(Self {
                accumulated_commitment_randomness,
                accumulated_proof_randomness,
            })
        })
    }
}

impl<E, PV> AbsorbableGadget<E::Fq> for RandomnessVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
{
    fn to_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<<E as PairingEngine>::Fq>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(
            self.accumulated_commitment_randomness,
            self.accumulated_proof_randomness
        )
    }
}

/// The [`Proof`][proof] of the [`AtomicASForMarlinPCVerifierGadget`][as_for_marlin_pc_verifier].
///
/// [proof]: crate::constraints::ASVerifierGadget::Proof
/// [as_for_marlin_pc_verifier]: crate::marlin_pc_as::constraints::AtomicASForMarlinPCVerifierGadget
pub struct ProofVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    /// The randomness used to apply zero-knowledge to the accumulated commitment and proof.
    pub(crate) randomness: Option<RandomnessVar<E, PV>>,
}

impl<E, PV> AllocVar<Option<Randomness<E>>, E::Fq> for ProofVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
{
    fn new_variable<T: Borrow<Option<Randomness<E>>>>(
        cs: impl Into<Namespace<<E as PairingEngine>::Fq>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|randomness| {
            let randomness = randomness
                .borrow()
                .as_ref()
                .map(|r| RandomnessVar::new_variable(ns.clone(), || Ok(r.clone()), mode))
                .transpose()?;

            Ok(Self { randomness })
        })
    }
}

impl<E, PV> AbsorbableGadget<E::Fq> for ProofVar<E, PV>
where
    E: PairingEngine,
    PV: PairingVar<E, E::Fq>,
    PV::G1Var: AbsorbableGadget<E::Fq>,
{
    fn to_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<<E as PairingEngine>::Fq>>, SynthesisError> {
        self.randomness.to_sponge_field_elements()
    }
}
