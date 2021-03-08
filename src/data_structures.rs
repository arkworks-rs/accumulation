use crate::AccumulationScheme;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::io::{Read, Write};

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
    /// Return references to the instances of `InstanceWitnessPair`s.
    pub fn instances<'a>(
        pairs: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = &'a Instance>
    where
        Self: 'a,
    {
        pairs.into_iter().map(|p| &p.instance)
    }

    /// Return the `InstanceWitnessPairRef`s to `InstanceWitnessPair`s.
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

    /// Return the `InstanceWitnessPairRef` to the `InstanceWitnessPair`.
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

/// The `AccumulatorInstance` and `AccumulatorWitness` of an `AccumulationScheme`.
pub type Accumulator<CF, S, A> = InstanceWitnessPair<
    <A as AccumulationScheme<CF, S>>::AccumulatorInstance,
    <A as AccumulationScheme<CF, S>>::AccumulatorWitness,
>;

/// References to the `AccumulatorInstance` and `AccumulatorWitness` of an `AccumulationScheme`.
pub type AccumulatorRef<'a, CF, S, A> = InstanceWitnessPairRef<
    'a,
    <A as AccumulationScheme<CF, S>>::AccumulatorInstance,
    <A as AccumulationScheme<CF, S>>::AccumulatorWitness,
>;

/// The `InputInstance` and `InputWitness` of an `AccumulationScheme`.
pub type Input<CF, S, A> = InstanceWitnessPair<
    <A as AccumulationScheme<CF, S>>::InputInstance,
    <A as AccumulationScheme<CF, S>>::InputWitness,
>;

/// References to the `InputInstance` and `InputWitness` of an `AccumulationScheme`.
pub type InputRef<'a, CF, S, A> = InstanceWitnessPairRef<
    'a,
    <A as AccumulationScheme<CF, S>>::InputInstance,
    <A as AccumulationScheme<CF, S>>::InputWitness,
>;
