use crate::hp_as::constraints::{
    InputInstanceVar as HPInputInstanceVar, ProofVar as HPProofVar,
    VerifierKeyVar as HPVerifierKeyVar,
};
use crate::r1cs_nark_as::data_structures::{
    AccumulatorInstance, InputInstance, Proof, ProofRandomness, VerifierKey,
};
use crate::r1cs_nark_as::r1cs_nark::{FirstRoundMessage, FirstRoundMessageRandomness};
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::UInt8;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::{collect_sponge_field_elements_gadget, Absorb};
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;
use ark_std::vec::Vec;

/// The [`VerifierKey`][vk] of the [`ASForR1CSNarkVerifierGadget`][as_for_r1cs_nark_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [as_for_r1cs_nark_verifier]: crate::r1cs_nark_as::constraints::ASForR1CSNarkVerifierGadget
pub struct VerifierKeyVar<CF: PrimeField> {
    /// The number of public input (i.e. instance) variables.
    pub(crate) num_instance_variables: usize,

    /// The verifier key for accumulation scheme for Hadamard Products.
    pub(crate) hp_as_vk: HPVerifierKeyVar<CF>,

    /// Hash of the matrices compute for the nark.
    pub(crate) nark_matrices_hash: Vec<FpVar<CF>>,

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

            let num_instance_variables = vk.num_instance_variables;

            let hp_as_vk_var =
                HPVerifierKeyVar::new_variable(ns.clone(), || Ok(vk.num_constraints), mode)?;

            let nark_matrices_hash = Vec::<CF>::new();
            vk.nark_matrices_hash
                .as_ref()
                .to_sponge_field_elements::<CF>(&mut nark_matrices_hash);
            let nark_matrices_hash_var = nark_matrices_hash
                .into_iter()
                .map(|f: CF| FpVar::new_variable(ns.clone(), || Ok(f), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let as_matrices_hash = Vec::<CF>::new();
            vk.as_matrices_hash
                .as_ref()
                .to_sponge_field_elements::<CF>(&mut as_matrices_hash);
            let as_matrices_hash_var = as_matrices_hash
                .into_iter()
                .map(|f: CF| FpVar::new_variable(ns.clone(), || Ok(f), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                num_instance_variables: num_instance_variables,
                hp_as_vk: hp_as_vk_var,
                nark_matrices_hash: nark_matrices_hash_var,
                as_matrices_hash: as_matrices_hash_var,
            })
        })
    }
}

impl<CF: PrimeField> AbsorbGadget<CF> for VerifierKeyVar<CF> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        let num_instance_variables = FpVar::Constant(CF::from(self.num_instance_variables as u64));
        collect_sponge_field_elements_gadget!(
            num_instance_variables,
            self.hp_as_vk,
            self.nark_matrices_hash,
            self.as_matrices_hash
        )
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<CF>>, SynthesisError> {
        todo!()
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

impl<G, C> AbsorbGadget<ConstraintF<G>> for FirstRoundMessageVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.randomness
        )
    }

    fn to_sponge_bytes(
        &self,
    ) -> Result<Vec<ark_r1cs_std::prelude::UInt8<ConstraintF<G>>>, SynthesisError> {
        todo!()
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

impl<G, C> AbsorbGadget<ConstraintF<G>> for FirstRoundMessageRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
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

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<ConstraintF<G>>>, SynthesisError> {
        todo!()
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
    pub r1cs_input: Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,

    /// The sigma protocol's prover commitment of the NARK.
    pub first_round_message: FirstRoundMessageVar<G, C>,
}

impl<G, C> AbsorbGadget<ConstraintF<G>> for InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        let mut r1cs_input_bytes = Vec::new();
        for elem in &self.r1cs_input {
            r1cs_input_bytes.append(&mut elem.to_bytes()?);
        }

        collect_sponge_field_elements_gadget!(r1cs_input_bytes, self.first_round_message)
    }

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<ConstraintF<G>>>, SynthesisError> {
        todo!()
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
                .map(|elem| {
                    NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::new_variable(
                        ns.clone(),
                        || Ok(elem),
                        mode,
                    )
                })
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
    pub(crate) r1cs_input: Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_a: C,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_b: C,

    /// Pedersen commitment to the `Az` vector.
    pub(crate) comm_c: C,

    /// The Hadamard product accumulation scheme input instance.
    pub(crate) hp_instance: HPInputInstanceVar<G, C>,
}

impl<G, C> AbsorbGadget<ConstraintF<G>> for AccumulatorInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
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

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<ConstraintF<G>>>, SynthesisError> {
        todo!()
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
                .map(|elem| {
                    NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::new_variable(
                        ns.clone(),
                        || Ok(elem),
                        mode,
                    )
                })
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
    pub(crate) r1cs_r_input: Vec<NonNativeFieldVar<G::ScalarField, ConstraintF<G>>>,

    /// Pedersen commitment to the vector that blinds the witness in `Az`.
    pub(crate) comm_r_a: C,

    /// Pedersen commitment to the vector that blinds the witness in `Bz`.
    pub(crate) comm_r_b: C,

    /// Pedersen commitment to the vector that blinds the witness in `Cz`.
    pub(crate) comm_r_c: C,
}

impl<G, C> AbsorbGadget<ConstraintF<G>> for ProofRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbGadget<ConstraintF<G>>,
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

    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<ConstraintF<G>>>, SynthesisError> {
        todo!()
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
                .map(|elem| {
                    NonNativeFieldVar::<G::ScalarField, ConstraintF<G>>::new_variable(
                        ns.clone(),
                        || Ok(elem),
                        mode,
                    )
                })
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
