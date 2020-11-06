use crate::AidedAccumulationScheme;

/// The accumulator of an aided accumulation scheme.
#[derive(Derivative)]
#[derivative(Clone(bound = "A: AidedAccumulationScheme"))]
pub struct Accumulator<A: AidedAccumulationScheme> {
    /// The instance of the accumulator.
    pub instance: A::AccumulatorInstance,

    /// The witness of the accumulator
    pub witness: A::AccumulatorWitness,
}

impl<A: AidedAccumulationScheme + ?Sized> Accumulator<A> {
    /// Extract the accumulator instances out of a list of accumulators.
    pub fn instances<'a>(
        accumulators: impl IntoIterator<Item = &'a Self>,
    ) -> impl Iterator<Item = &'a A::AccumulatorInstance> {
        accumulators.into_iter().map(|a| &a.instance)
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
    ) -> impl Iterator<Item = &'a A::InputInstance> {
        inputs.into_iter().map(|i| &i.instance)
    }
}
