use crate::AidedAccumulationScheme;
use std::vec::Vec;

/// The accumulator of an aided accumulation scheme.
#[derive(Derivative)]
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
    ) -> Vec<&'a A::AccumulatorInstance>
    where
        A: 'a,
    {
        let mut instances = Vec::new();
        for accumulator in accumulators {
            instances.push(&accumulator.instance)
        }
        instances
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
    pub fn instances<'a>(inputs: impl IntoIterator<Item = &'a Self>) -> Vec<&'a A::InputInstance>
    where
        A: 'a,
    {
        let mut instances = Vec::new();
        for input in inputs {
            instances.push(&input.instance)
        }
        instances
    }
}
