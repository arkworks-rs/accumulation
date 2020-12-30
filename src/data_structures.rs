use crate::{AccumulationScheme, AidedAccumulationScheme};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::io::{Read, Write};

/// The accumulator of an aided accumulation scheme.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "A: AidedAccumulationScheme"))]
pub struct Accumulator<A: AidedAccumulationScheme> {
    /// The instance of the accumulator.
    pub instance: A::AccumulatorInstance,

    /// The witness of the accumulator
    pub witness: A::AccumulatorWitness,
}

impl<A: AidedAccumulationScheme> Accumulator<A> {
    /// Extract the accumulator instances out of a list of accumulators.
    pub fn instances<'a>(
        accumulators: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = &'a A::AccumulatorInstance>
    where
        A: 'a,
    {
        accumulators.into_iter().map(|a| &a.instance)
    }
}

impl<A: AccumulationScheme> Accumulator<A> {
    /// Obtain an accumulator from the accumulator instance for accumulation schemes.
    pub fn from_instance(instance: A::AccumulatorInstance) -> Self {
        Accumulator {
            instance,
            witness: (),
        }
    }
}

/// The input of an aided accumulation scheme.
#[derive(Derivative)]
#[derivative(Clone(bound = "A: AidedAccumulationScheme"))]
pub struct Input<A: AidedAccumulationScheme> {
    /// The instance of the input.
    pub instance: A::InputInstance,

    /// The witness of the input.
    pub witness: A::InputWitness,
}

impl<A: AidedAccumulationScheme> Input<A> {
    /// Extract the input instances out of a list of inputs.
    pub fn instances<'a>(
        inputs: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = &'a A::InputInstance>
    where
        A: 'a,
    {
        inputs.into_iter().map(|i| &i.instance)
    }
}

impl<A: AccumulationScheme> Input<A> {
    /// Obtain input from the input instance for accumulation schemes.
    pub fn from_instance(instance: A::InputInstance) -> Self {
        Input {
            instance,
            witness: (),
        }
    }
}
