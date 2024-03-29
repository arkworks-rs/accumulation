use crate::hp_as::data_structures::{ProductPolynomialCommitment, Proof, ProofHidingCommitments};
use crate::hp_as::InputInstance;
use crate::ConstraintF;

use ark_ec::AffineCurve;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::collect_sponge_field_elements_gadget;
use ark_sponge::constraints::AbsorbableGadget;
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;
use ark_std::vec::Vec;

/// The [`VerifierKey`][vk] of the [`ASForHPVerifierGadget`][as_for_hp_verifier].
///
/// [vk]: crate::constraints::ASVerifierGadget::VerifierKey
/// [as_for_hp_verifier]: crate::hp_as::constraints::ASForHPVerifierGadget
pub struct VerifierKeyVar<CF: PrimeField> {
    /// The maximum supported vector length of the Hadamard product relation.
    pub(crate) num_supported_elems: FpVar<CF>,
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

impl<CF: PrimeField> AbsorbableGadget<CF> for VerifierKeyVar<CF> {
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<CF>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.num_supported_elems)
    }
}

/// The [`InputInstance`][input] of the [`ASForHPVerifierGadget`][as_for_hp_verifier].
///
/// [input]: crate::constraints::ASVerifierGadget::InputInstance
/// [as_for_hp_verifier]: crate::hp_as::constraints::ASForHPVerifierGadget
pub struct InputInstanceVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Pedersen commitment to the `a` vector of the Hadamard product relation.
    pub comm_1: C,

    /// Pedersen commitment to the `b` vector of the Hadamard product relation.
    pub comm_2: C,

    /// Pedersen commitment to the `a ◦ b` vector of the Hadamard product relation.
    pub comm_3: C,

    #[doc(hidden)]
    pub _curve: PhantomData<G>,
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

/// The [`Proof`][proof] of the [`ASForHPVerifierGadget`][as_for_hp_verifier].
///
/// [proof]: crate::constraints::ASVerifierGadget::Proof
/// [as_for_hp_verifier]: crate::hp_as::constraints::ASForHPVerifierGadget
pub struct ProofVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Pedersen commitments to each coefficient vector of the product polynomial
    /// `a(X, µ) ◦ b(X)`, excluding `n-1`th coefficient (0-index)
    pub(crate) product_poly_comm: ProductPolynomialCommitmentVar<G, C>,

    /// Pedersen commitments to the random vectors used to apply zero-knowledge to the vectors
    /// of the Hadamard product relation.
    pub(crate) hiding_comms: Option<ProofHidingCommitmentsVar<G, C>>,

    #[doc(hidden)]
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
            let product_poly_comm = ProductPolynomialCommitmentVar::new_variable(
                ns.clone(),
                || Ok(&proof.borrow().product_poly_comm),
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
                product_poly_comm,
                hiding_comms,
                _curve: PhantomData,
            })
        })
    }
}

/// The Pedersen commitments to each coefficient vector of the product polynomial `a(X, µ) ◦ b(X)`.
/// Excludes `n-1`th commitment (0-index)
pub(crate) struct ProductPolynomialCommitmentVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Pedersen commitments to the first `n-1` coefficients of the lower powers.
    pub(crate) low: Vec<C>,

    /// Pedersen commitments to the last `n-1` coefficients of the higher powers.
    pub(crate) high: Vec<C>,

    #[doc(hidden)]
    pub(crate) _curve: PhantomData<G>,
}

impl<G, C> AllocVar<ProductPolynomialCommitment<G>, ConstraintF<G>>
    for ProductPolynomialCommitmentVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    fn new_variable<T: Borrow<ProductPolynomialCommitment<G>>>(
        cs: impl Into<Namespace<ConstraintF<G>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        f().and_then(|product_poly_comm| {
            let product_poly_comm_low = product_poly_comm
                .borrow()
                .low
                .iter()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            let product_poly_comm_high = product_poly_comm
                .borrow()
                .high
                .iter()
                .map(|comm| C::new_variable(ns.clone(), || Ok(comm.clone()), mode))
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            Ok(Self {
                low: product_poly_comm_low,
                high: product_poly_comm_high,
                _curve: PhantomData,
            })
        })
    }
}

impl<G, C> AbsorbableGadget<ConstraintF<G>> for ProductPolynomialCommitmentVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>> + AbsorbableGadget<ConstraintF<G>>,
{
    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<ConstraintF<G>>>, SynthesisError> {
        collect_sponge_field_elements_gadget!(self.low, self.high)
    }
}

/// The Pedersen commitments to the random vectors used to apply zero-knowledge to the vectors of
/// the Hadamard product relation.
pub(crate) struct ProofHidingCommitmentsVar<G, C>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, ConstraintF<G>>,
{
    /// Pedersen commitment to the random vector that hides the `a` vector of the Hadamard
    /// product relation.
    pub(crate) comm_1: C,

    /// Pedersen commitment to the random vector that hides the `b` vector of the Hadamard
    /// product relation.
    pub(crate) comm_2: C,

    /// Pedersen commitment to the cross term randomness vector
    pub(crate) comm_3: C,

    #[doc(hidden)]
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
