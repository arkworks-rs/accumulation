use crate::AccumulationScheme;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::io::{Read, Write};
use ark_std::rand::RngCore;

// Useful type alias for implementations.
#[cfg(feature = "impl")]
use {ark_ec::AffineCurve, ark_ff::Field};

#[cfg(feature = "impl")]
pub(crate) type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;

/// A pair consisting of references to an instance and witness.
pub struct InstanceWitnessPairRef<
    'a,
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize,
> {
    /// The reference to the instance of a pair.
    pub instance: &'a Instance,

    /// The reference to the witness of a pair.
    pub witness: &'a Witness,
}

impl<'a, Instance, Witness> InstanceWitnessPairRef<'a, Instance, Witness>
where
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize,
{
    /// Extract the accumulator instances out of a list of accumulators.
    pub fn instances(pairs: impl IntoIterator<Item = Self>) -> impl Iterator<Item = &'a Instance>
    where
        Self: 'a,
    {
        pairs.into_iter().map(|p| p.instance)
    }
}

/// A pair consisting of an instance and witness.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize,
"))]
pub struct InstanceWitnessPair<
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize,
> {
    /// The instance of the pair.
    pub instance: Instance,

    /// The witness of the pair.
    pub witness: Witness,
}

impl<Instance, Witness> InstanceWitnessPair<Instance, Witness>
where
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize,
{
    /// Returns a reference for each instance in the list of [`InstanceWitnessPair`]s.
    pub fn instances<'a>(
        pairs: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = &'a Instance>
    where
        Self: 'a,
    {
        pairs.into_iter().map(|p| &p.instance)
    }

    /// Returns a [`InstanceWitnessPairRef`] for each [`InstanceWitnessPair`] reference.
    pub fn map_to_refs<'a>(
        pairs: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = InstanceWitnessPairRef<'a, Instance, Witness>>
    where
        Self: 'a,
    {
        pairs.into_iter().map(|p| InstanceWitnessPairRef {
            instance: &p.instance,
            witness: &p.witness,
        })
    }

    /// Returns the [`InstanceWitnessPairRef`] for a [`InstanceWitnessPair`] reference.
    pub fn as_ref(&self) -> InstanceWitnessPairRef<'_, Instance, Witness> {
        InstanceWitnessPairRef {
            instance: &self.instance,
            witness: &self.witness,
        }
    }
}

impl<Instance, Witness> Default for InstanceWitnessPair<Instance, Witness>
where
    Instance: Clone + CanonicalSerialize + CanonicalDeserialize + Default,
    Witness: Clone + CanonicalSerialize + CanonicalDeserialize + Default,
{
    fn default() -> Self {
        Self {
            instance: Instance::default(),
            witness: Witness::default(),
        }
    }
}

/// A pair of [`AccumulatorInstance`][instance] and [`AccumulatorWitness`][witness].
///
/// [instance]: AccumulationScheme::AccumulatorInstance
/// [witness]: AccumulationScheme::AccumulatorWitness
pub type Accumulator<CF, A> = InstanceWitnessPair<
    <A as AccumulationScheme<CF>>::AccumulatorInstance,
    <A as AccumulationScheme<CF>>::AccumulatorWitness,
>;

/// A pair of references to an [`AccumulatorInstance`][instance] and
/// [`AccumulatorWitness`][witness].
///
/// [instance]: AccumulationScheme::AccumulatorInstance
/// [witness]: AccumulationScheme::AccumulatorWitness
pub type AccumulatorRef<'a, CF, A> = InstanceWitnessPairRef<
    'a,
    <A as AccumulationScheme<CF>>::AccumulatorInstance,
    <A as AccumulationScheme<CF>>::AccumulatorWitness,
>;

/// A pair of [`InputInstance`][instance] and [`InputWitness`][witness].
///
/// [instance]: AccumulationScheme::InputInstance
/// [witness]: AccumulationScheme::InputWitness
pub type Input<CF, A> = InstanceWitnessPair<
    <A as AccumulationScheme<CF>>::InputInstance,
    <A as AccumulationScheme<CF>>::InputWitness,
>;

/// A pair of references to an [`InputInstance`][instance] and [`InputWitness`][witness].
///
/// [instance]: AccumulationScheme::InputInstance
/// [witness]: AccumulationScheme::InputWitness
pub type InputRef<'a, CF, A> = InstanceWitnessPairRef<
    'a,
    <A as AccumulationScheme<CF>>::InputInstance,
    <A as AccumulationScheme<CF>>::InputWitness,
>;

/// Specifies the zero-knowledge configuration for an accumulation.
pub enum MakeZK<'a> {
    /// Enable zero-knowledge accumulation.
    Enabled(&'a mut dyn RngCore),

    /// Disable zero-knowledge accumulation.
    Disabled,
}

impl<'a> MakeZK<'a> {
    /// Converts the MakeZK parameter to a (make_zk_enabled, rng)
    pub fn into_components(self) -> (bool, Option<&'a mut dyn RngCore>) {
        match self {
            MakeZK::Enabled(rng) => (true, Some(rng)),
            MakeZK::Disabled => (false, None),
        }
    }
}
