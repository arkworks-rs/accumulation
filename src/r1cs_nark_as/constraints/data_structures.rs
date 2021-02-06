use crate::constraints::{ConstraintF, NNFieldVar};
use crate::hp_as::constraints::data_structures::{
    InputInstanceVar as HPInputInstanceVar, ProofVar as HPProofVar,
};
use crate::r1cs_nark::data_structures::{FirstRoundMessage, IndexInfo};
use crate::r1cs_nark_as::data_structures::{
    AccumulatorInstance, InputInstance, Proof, ProofRandomness, VerifierKey,
};
use ark_ec::AffineCurve;
use ark_ff::{PrimeField, ToConstraintField};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use std::borrow::Borrow;
use std::marker::PhantomData;

pub struct IndexInfoVar<CF: PrimeField> {
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
                .to_field_elements()
                .unwrap()
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

pub struct VerifierKeyVar<CF: PrimeField> {
    pub nark_index: IndexInfoVar<CF>,
    pub as_matrices_hash: Vec<FpVar<CF>>,
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
                .to_field_elements()
                .unwrap()
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

pub struct FirstRoundMessageVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    pub comm_a: C,
    pub comm_b: C,
    pub comm_c: C,
    pub comm_r_a: Option<C>,
    pub comm_r_b: Option<C>,
    pub comm_r_c: Option<C>,
    pub comm_1: Option<C>,
    pub comm_2: Option<C>,

    pub _affine_phantom: PhantomData<G>,
}

impl<G, C> FirstRoundMessageVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        sponge.absorb(self.comm_a.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_b.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_c.to_constraint_field()?.as_slice())?;

        for comm in [
            self.comm_r_a.as_ref(),
            self.comm_r_b.as_ref(),
            self.comm_r_c.as_ref(),
            self.comm_1.as_ref(),
            self.comm_2.as_ref(),
        ]
        .iter()
        {
            if let Some(comm) = comm {
                sponge.absorb(&[FpVar::one()])?;
                sponge.absorb(comm.to_constraint_field()?.as_slice())?;
            } else {
                sponge.absorb(&[FpVar::zero()])?;
            }
        }

        Ok(())
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

            let comm_r_a = first_round_msg
                .comm_r_a
                .as_ref()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .transpose()?;

            let comm_r_b = first_round_msg
                .comm_r_b
                .as_ref()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .transpose()?;

            let comm_r_c = first_round_msg
                .comm_r_c
                .as_ref()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .transpose()?;

            let comm_1 = first_round_msg
                .comm_1
                .as_ref()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .transpose()?;

            let comm_2 = first_round_msg
                .comm_2
                .as_ref()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .transpose()?;

            Ok(Self {
                comm_a,
                comm_b,
                comm_c,
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

pub struct InputInstanceVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    pub r1cs_input: Vec<NNFieldVar<G>>,
    pub first_round_message: FirstRoundMessageVar<G, C>,
    pub make_zk: bool,
}

impl<G, C> InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        let mut r1cs_input_bytes = Vec::new();
        for elem in &self.r1cs_input {
            r1cs_input_bytes.append(&mut elem.to_bytes()?);
        }
        sponge.absorb(r1cs_input_bytes.to_constraint_field()?.as_slice())?;
        self.first_round_message.absorb_into_sponge(sponge)?;
        sponge.absorb(&[FpVar::from(Boolean::Constant(self.make_zk))])?;

        Ok(())
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
                make_zk: instance.make_zk,
            })
        })
    }
}

pub struct AccumulatorInstanceVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    pub r1cs_input: Vec<NNFieldVar<G>>,
    pub comm_a: C,
    pub comm_b: C,
    pub comm_c: C,
    pub hp_instance: HPInputInstanceVar<G, C>,
}

impl<G, C> AccumulatorInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        let mut r1cs_input_bytes = Vec::new();
        for elem in &self.r1cs_input {
            r1cs_input_bytes.append(&mut elem.to_bytes()?);
        }
        sponge.absorb(r1cs_input_bytes.to_constraint_field()?.as_slice())?;

        sponge.absorb(self.comm_a.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_b.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_c.to_constraint_field()?.as_slice())?;

        self.hp_instance.absorb_into_sponge(sponge)?;

        Ok(())
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

pub struct ProofRandomnessVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    pub r1cs_r_input: Vec<NNFieldVar<G>>,
    pub comm_r_a: C,
    pub comm_r_b: C,
    pub comm_r_c: C,
}

impl<G, C> ProofRandomnessVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + ToConstraintFieldGadget<ConstraintF<G>>,
{
    pub fn absorb_into_sponge<S>(&self, sponge: &mut S) -> Result<(), SynthesisError>
    where
        S: CryptographicSpongeVar<ConstraintF<G>>,
    {
        for elem in &self.r1cs_r_input {
            sponge.absorb(elem.to_constraint_field()?.as_slice())?;
        }

        sponge.absorb(self.comm_r_a.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_r_b.to_constraint_field()?.as_slice())?;
        sponge.absorb(self.comm_r_c.to_constraint_field()?.as_slice())?;

        Ok(())
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

pub struct ProofVar<G: AffineCurve, C: CurveVar<G::Projective, ConstraintF<G>>> {
    pub hp_proof: HPProofVar<G, C>,
    pub randomness: Option<ProofRandomnessVar<G, C>>,
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
