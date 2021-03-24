use crate::constraints::NNFieldVar;
use crate::hp_as::constraints::{InputInstanceVar as HPInputInstanceVar, ProofVar as HPProofVar};
use crate::r1cs_nark_as::data_structures::{
    AccumulatorInstance, InputInstance, Proof, ProofRandomness, VerifierKey,
};
use crate::r1cs_nark_as::r1cs_nark::{FirstRoundMessage, FirstRoundMessageRandomness, IndexInfo};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::AbsorbableGadget;
use ark_sponge::{collect_sponge_field_elements_gadget, Absorbable};
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;
use ark_std::vec::Vec;

pub(crate) struct IndexInfoVar<CF: PrimeField> {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,

    /// The number of constraints.
    pub num_constraints: usize,

    /// The number of public input (i.e. instance) variables.
    pub num_instance_variables: usize,

    /// Hash of the matrices.
    pub matrices_hash: Vec<FpVar<CF>>,
}

impl<CF: PrimeField> AllocVar<IndexInfo, CF> for IndexInfoVar<CF> {
    fn new_variable<T: Borrow<IndexInfo>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|index_info| {
            let index_info = index_info.borrow();
            let matrices_hash = index_info
                .matrices_hash
                .as_ref()
                .to_sponge_field_elements()
                .into_iter()
                .map(|f: CF| FpVar::new_variable(ns.clone(), || Ok(f), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                num_variables: index_info.num_variables,
                num_constraints: index_info.num_constraints,
                num_instance_variables: index_info.num_instance_variables,
                matrices_hash,
            })
        })
    }
}

/// The [`VerifierKey`][vk] of the [`ASForR1CSNarkVerifierGadget`][as_for_r1cs_nark_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [as_for_r1cs_nark_verifier]: crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget
pub struct VerifierKeyVar<CF: PrimeField> {
    /// Information about the index.
    pub(crate) nark_index: IndexInfoVar<CF>,

    /// Hash of the matrices computed for the accumulation scheme.
    pub(crate) as_matrices_hash: Vec<FpVar<CF>>,
}

impl<CF: PrimeField> AllocVar<VerifierKey, CF> for VerifierKeyVar<CF> {
    fn new_variable<T: Borrow<VerifierKey>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|vk| {
            let vk = vk.borrow();

            let nark_index =
                IndexInfoVar::new_variable(ns.clone(), || Ok(vk.nark_index.clone()), mode)?;

            let as_matrices_hash = vk
                .as_matrices_hash
                .as_ref()
                .to_sponge_field_elements()
                .into_iter()
                .map(|f: CF| FpVar::new_variable(ns.clone(), || Ok(f), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                nark_index,
                as_matrices_hash,
            })
        })
    }
}

/// The sigma protocol's prover commitment.
pub struct FirstRoundMessageVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: C,

    /// Pedersen commitment to the `Bz` vector.
    pub(crate) comm_b: C,

    /// Pedersen commitment to the `Cz` vector.
    pub(crate) comm_c: C,

    /// The randomness used for the commitment.
    pub(crate) randomness: Option<FirstRoundMessageRandomnessVar<G, C>>,

    #[doc(hidden)]
    pub(crate) _affine_phantom: PhantomData<G>,
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for FirstRoundMessageVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.randomness
        )
    }
}

impl<G, C> AllocVar<FirstRoundMessage<G>, ConstraintF<G>> for FirstRoundMessageVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<FirstRoundMessage<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|first_round_msg| {
            let first_round_msg = first_round_msg.borrow();

            let comm_a = C::new_variable(ns.clone(), || Ok(first_round_msg.comm_a.clone()), mode)?;
            let comm_b = C::new_variable(ns.clone(), || Ok(first_round_msg.comm_b.clone()), mode)?;
            let comm_c = C::new_variable(ns.clone(), || Ok(first_round_msg.comm_c.clone()), mode)?;

            let randomness = first_round_msg
                .randomness
                .clone()
                .map(|r| FirstRoundMessageRandomnessVar::new_variable(ns.clone(), || Ok(r), mode))
                .transpose()?;

            Ok(Self {
                comm_a,
                comm_b,
                comm_c,
                randomness,
                _affine_phantom: PhantomData,
            })
        })
    }
}

/// The sigma protocol's prover commitment randomness.
pub struct FirstRoundMessageRandomnessVar<
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
> {
    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: C,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: C,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: C,

    /// Pedersen commitment to the first cross term randomness vector.
    pub(crate) comm_1: C,

    /// Pedersen commitment to the second cross term randomness vector.
    pub(crate) comm_2: C,

    #[doc(hidden)]
    pub(crate) _affine_phantom: PhantomData<G>,
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for FirstRoundMessageRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        )
    }
}

impl<G, C> AllocVar<FirstRoundMessageRandomness<G>, ConstraintF<G>>
    for FirstRoundMessageRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<FirstRoundMessageRandomness<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|first_round_msg| {
            let first_round_msg_randomness = first_round_msg.borrow();

            let comm_r_a =
                C::new_variable(ns.clone(), || Ok(first_round_msg_randomness.comm_r_a), mode)?;
            let comm_r_b =
                C::new_variable(ns.clone(), || Ok(first_round_msg_randomness.comm_r_b), mode)?;
            let comm_r_c =
                C::new_variable(ns.clone(), || Ok(first_round_msg_randomness.comm_r_c), mode)?;
            let comm_1 =
                C::new_variable(ns.clone(), || Ok(first_round_msg_randomness.comm_1), mode)?;
            let comm_2 =
                C::new_variable(ns.clone(), || Ok(first_round_msg_randomness.comm_2), mode)?;

            Ok(Self {
                comm_r_a,
                comm_r_b,
                comm_r_c,
                comm_1,
                comm_2,
                _affine_phantom: PhantomData,
            })
        })
    }
}

/// The [`InputInstance`][input_instance] of the
/// [`ASForR1CSNarkVerifierGadget`][as_for_r1cs_nark_verifier].
///
/// [input_instance]: crate::constraints::ASVerifierGadget::InputInstance
/// [as_for_r1cs_nark_verifier]: crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget
pub struct InputInstanceVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    /// An R1CS input.
    pub r1cs_input: Vec<NNFieldVar<G>>,

    /// The sigma protocol's prover commitment of the NARK.
    pub first_round_message: FirstRoundMessageVar<G, C>,
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        let mut r1cs_input_bytes = Vec::new();
        for elem in &self.r1cs_input {
            r1cs_input_bytes.append(&mut elem.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(
            r1cs_input_bytes,
            self.first_round_message
        )
    }
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
        f().and_then(|instance| {
            let instance = instance.borrow();
            let r1cs_input = instance
                .r1cs_input
                .clone()
                .into_iter()
                .map(|elem| NNFieldVar::<G>::new_variable(ns.clone(), || Ok(elem), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let first_round_message = FirstRoundMessageVar::new_variable(
                ns.clone(),
                || Ok(instance.first_round_message.clone()),
                mode,
            )?;

            Ok(Self {
                r1cs_input,
                first_round_message,
            })
        })
    }
}

/// The [`AccumulatorInstance`][acc_instance] of the
/// [`ASForR1CSNarkVerifierGadget`][as_for_r1cs_nark_verifier].
///
/// [acc_instance]: crate::constraints::ASVerifierGadget::AccumulatorInstance
/// [as_for_r1cs_nark_verifier]: crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget
pub struct AccumulatorInstanceVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    /// An input for the indexed relation.
    pub(crate) r1cs_input: Vec<NNFieldVar<G>>,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: C,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_b: C,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_c: C,

    /// The Hadamard product accumulation scheme input instance.
    pub(crate) hp_instance: HPInputInstanceVar<G, C>,
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for AccumulatorInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        let mut r1cs_input_bytes = Vec::new();
        for elem in &self.r1cs_input {
            r1cs_input_bytes.append(&mut elem.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(
            r1cs_input_bytes,
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.hp_instance
        )
    }
}

impl<G, C> AllocVar<AccumulatorInstance<G>, ConstraintF<G>> for AccumulatorInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<AccumulatorInstance<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|instance| {
            let instance = instance.borrow();

            let r1cs_input = instance
                .r1cs_input
                .clone()
                .into_iter()
                .map(|elem| NNFieldVar::<G>::new_variable(ns.clone(), || Ok(elem), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;
            let comm_a = C::new_variable(ns.clone(), || Ok(instance.comm_a.clone()), mode)?;
            let comm_b = C::new_variable(ns.clone(), || Ok(instance.comm_b.clone()), mode)?;
            let comm_c = C::new_variable(ns.clone(), || Ok(instance.comm_c.clone()), mode)?;
            let hp_instance = HPInputInstanceVar::new_variable(
                ns.clone(),
                || Ok(instance.hp_instance.clone()),
                mode,
            )?;

            Ok(Self {
                r1cs_input,
                comm_a,
                comm_b,
                comm_c,
                hp_instance,
            })
        })
    }
}

/// The [`Proof`][proof_var] of the [`ASForR1CSNarkVerifierGadget`][as_for_r1cs_nark_verifier].
///
/// [proof_var]: crate::constraints::ASVerifierGadget::Proof
/// [as_for_r1cs_nark_verifier]: crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget
pub struct ProofVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    /// The Hadamard product accumulation scheme proof.
    pub(crate) hp_proof: HPProofVar<G, C>,

    /// Randomness or their commitments used to blind the vectors of the indexed relation.
    pub(crate) randomness: Option<ProofRandomnessVar<G, C>>,
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
            let proof = proof.borrow();

            let hp_proof =
                HPProofVar::new_variable(ns.clone(), || Ok(proof.hp_proof.clone()), mode)?;

            let randomness = proof
                .randomness
                .as_ref()
                .map(|randomness| {
                    ProofRandomnessVar::new_variable(ns.clone(), || Ok(randomness.clone()), mode)
                })
                .transpose()?;

            Ok(Self {
                hp_proof,
                randomness,
            })
        })
    }
}

/// The randomness or their commitments used to blind the vectors of the indexed relation.
pub(crate) struct ProofRandomnessVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    /// Randomness used to blind the R1CS input.
    pub(crate) r1cs_r_input: Vec<NNFieldVar<G>>,

    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: C,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: C,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: C,
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for ProofRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        let mut r1cs_r_input_bytes = Vec::new();
        for elem in &self.r1cs_r_input {
            r1cs_r_input_bytes.append(&mut elem.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(
            r1cs_r_input_bytes,
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c
        )
    }
}

impl<G, C> AllocVar<ProofRandomness<G>, ConstraintF<G>> for ProofRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<ProofRandomness<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|randomness| {
            let randomness = randomness.borrow();

            let r1cs_r_input = randomness
                .r1cs_r_input
                .clone()
                .into_iter()
                .map(|elem| NNFieldVar::<G>::new_variable(ns.clone(), || Ok(elem), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let comm_r_a = C::new_variable(ns.clone(), || Ok(randomness.comm_r_a.clone()), mode)?;
            let comm_r_b = C::new_variable(ns.clone(), || Ok(randomness.comm_r_b.clone()), mode)?;
            let comm_r_c = C::new_variable(ns.clone(), || Ok(randomness.comm_r_c.clone()), mode)?;

            Ok(Self {
                r1cs_r_input,
                comm_r_a,
                comm_r_b,
                comm_r_c,
            })
        })
    }
}
