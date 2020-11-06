#![cfg_attr(not(feature = "std"), no_std)]

//! A crate for accumulation schemes.
#![deny(
    const_err,
    future_incompatible,
    missing_docs,
    non_shorthand_field_patterns,
    renamed_and_removed_lints,
    rust_2018_idioms,
    stable_features,
    trivial_casts,
    trivial_numeric_casts,
    unused,
    variant_size_differences,
    warnings
)]
#![forbid(unsafe_code)]

use crate::data_structures::{Accumulator, Input};
use rand_core::RngCore;

#[macro_use]
extern crate derivative;

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc as std;

/// Common data structures used by `AccumulationScheme` and `AidedAccumulationScheme`.
pub mod data_structures;

/// Common errors for `AccumulationScheme` and `AidedAccumulationScheme`.
pub mod error;

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// accumulates a stream of inputs into a single accumulator, which holds the necessary properties
/// to ensure each accumulated input satisfies the predicate. The prover also outputs a proof
/// attesting that the accumulator was computed correctly, which a verifier can check. At any
/// point, a decider use an accumulator to determine if each accumulated input satisfies the
/// predicate.
/// Accumulation schemes are aided accumulation schemes with empty witnesses. So, verifiers receive
/// entire accumulators and inputs.
pub trait AccumulationScheme:
    AidedAccumulationScheme<InputWitness = (), AccumulatorWitness = ()>
{
}

/// An interface for an aided accumulation scheme. In an aided accumulation scheme, accumulators
/// and inputs are split into instance, witness pairs. Verifiers no longer receive entire
/// accumulators or inputs but instead receive their respective instances.
pub trait AidedAccumulationScheme: Sized {
    /// The public parameters of the accumulation scheme's predicate.
    type PredicateParams: Clone;

    /// The index of the accumulation scheme's predicate.
    type PredicateIndex: Clone;

    /// The universal parameters for the accumulation scheme.
    type UniversalParams: Clone;

    /// The prover key, used to accumulate inputs and past accumulators and to prove that the
    /// new accumulator was computed correctly from the inputs and old accumulators.
    type ProverKey: Clone;

    /// The verifier key, used to check that an accumulator was computed correctly from the inputs
    /// and old accumulators.
    type VerifierKey: Clone;

    /// The decider key, used to establish whether each of the accumulated inputs satisfes the
    /// predicate.
    type DeciderKey: Clone;

    /// The instance of the input to be accumulated.
    type InputInstance: Clone;

    /// The witness of the input to be accumulated.
    type InputWitness: Clone;

    /// The instance of the accumulator.
    type AccumulatorInstance: Clone;

    /// The witness of the accumulator.
    type AccumulatorWitness: Clone;

    /// The proof, used to prove that the accumulator was properly computed.
    type Proof: Clone;

    /// The error type used in the scheme.
    type Error: ark_std::error::Error;

    /// Outputs the universal parameters of the accumulation scheme.
    fn generate(rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error>;

    /// Outputs the prover, verifier, and decider keys, specialized for a specific index of the
    /// predicate.
    fn index(
        universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error>;

    /// Accumulates the inputs and past accumulators. Additionally outputs the proof attesting
    /// that that the new accumulator was computed properly from the inputs and old accumulators.
    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = &'a Input<Self>>,
        accumulators: impl IntoIterator<Item = &'a Accumulator<Self>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a;

    /// Verifies using a proof that the new accumulator instance was computed properly from the
    /// input instances and old accumulator instances.
    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a;

    /// Determines whether an accumulator is valid, which means every accumulated input satisfies
    /// the predicate.
    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: &Accumulator<Self>,
    ) -> Result<bool, Self::Error>;
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::{Accumulator, Input};
    use crate::std::vec::Vec;
    use crate::AidedAccumulationScheme;
    use rand_core::RngCore;

    /// An interface for generating inputs and accumulators to test an accumulation scheme.
    pub trait AccumulationSchemeTestInput<A: AidedAccumulationScheme> {
        /// Parameters for setting up the test
        type TestParams;

        /// Parameters for generating the inputs and accumulators
        type InputParams;

        /// Sets up the test inputs. Establishes the parameters and index for the predicate. Also
        /// outputs the parameters to generate accumulators and inputs for the corresponding
        /// predicate index.
        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (Self::InputParams, A::PredicateParams, A::PredicateIndex);

        /// Generates `num_accumulators` starting accumulators.
        fn generate_starting_accumulators(
            input_params: &Self::InputParams,
            num_accumulators: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Accumulator<A>>;

        /// Generates `num_inputs` inputs for one accumulation.
        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<A>>;
    }

    pub struct TemplateParams {
        num_iterations: usize,
        num_starting_accumulators: usize,
        num_inputs_per_accumulation: usize,
        num_accumulations: usize,
    }

    /// For each iteration, runs the accumulation scheme for `num_accumulations` steps of proving
    /// and verifying and starts with `num_starting_accumulators` old accumulators.
    /// At the end of the iteration, the last accumulator is put through a single decider.
    /// The function will return whether all of the verifiers and deciders returned true
    /// from all of the iterations.
    pub fn test_template<A: AidedAccumulationScheme, I: AccumulationSchemeTestInput<A>>(
        template_params: &TemplateParams,
        test_params: &I::TestParams,
    ) -> Result<bool, A::Error> {
        assert!(template_params.num_iterations > 0);

        let mut rng = ark_ff::test_rng();
        let universal_params = A::generate(&mut rng)?;
        for _ in 0..template_params.num_iterations {
            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let (pk, vk, dk) = A::index(&universal_params, &predicate_params, &predicate_index)?;

            let mut old_accumulators = I::generate_starting_accumulators(
                &input_params,
                template_params.num_starting_accumulators,
                &mut rng,
            );
            assert_eq!(
                old_accumulators.len(),
                template_params.num_starting_accumulators
            );

            for i in 0..template_params.num_accumulations {
                let inputs = I::generate_inputs(
                    &input_params,
                    template_params.num_inputs_per_accumulation,
                    &mut rng,
                );
                assert_eq!(inputs.len(), template_params.num_inputs_per_accumulation);

                let (accumulator, proof) =
                    A::prove(&pk, &inputs, &old_accumulators, Some(&mut rng))?;
                if !A::verify(
                    &vk,
                    Input::instances(&inputs),
                    Accumulator::instances(&old_accumulators),
                    &accumulator.instance,
                    &proof,
                )? {
                    println!("{}", format!("Verify failed on accumulation {}", i));
                    return Ok(false);
                }

                old_accumulators.push(accumulator);
            }

            assert!(old_accumulators.len() > 0);
            if !A::decide(&dk, old_accumulators.last().unwrap())? {
                println!("Decide failed");
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn no_starting_accumulators_test<
        A: AidedAccumulationScheme,
        I: AccumulationSchemeTestInput<A>,
    >(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 0,
            num_inputs_per_accumulation: 1,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn no_inputs_test<A: AidedAccumulationScheme, I: AccumulationSchemeTestInput<A>>(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 1,
            num_inputs_per_accumulation: 0,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn base_test<A: AidedAccumulationScheme, I: AccumulationSchemeTestInput<A>>(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 1,
            num_inputs_per_accumulation: 1,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn multiple_starting_accumulators_test<
        A: AidedAccumulationScheme,
        I: AccumulationSchemeTestInput<A>,
    >(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 10,
            num_inputs_per_accumulation: 1,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn multiple_inputs_test<A: AidedAccumulationScheme, I: AccumulationSchemeTestInput<A>>(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 1,
            num_inputs_per_accumulation: 10,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn multiple_accumulations_test<
        A: AidedAccumulationScheme,
        I: AccumulationSchemeTestInput<A>,
    >(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 1,
            num_inputs_per_accumulation: 1,
            num_accumulations: 10,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn multiple_starting_accumulators_and_inputs_test<
        A: AidedAccumulationScheme,
        I: AccumulationSchemeTestInput<A>,
    >(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 10,
            num_inputs_per_accumulation: 10,
            num_accumulations: 1,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }

    pub fn multiple_starting_accumulators_inputs_and_accumulations_test<
        A: AidedAccumulationScheme,
        I: AccumulationSchemeTestInput<A>,
    >(
        test_params: &I::TestParams,
    ) -> Result<(), A::Error> {
        let template_params = TemplateParams {
            num_iterations: 50,
            num_starting_accumulators: 10,
            num_inputs_per_accumulation: 10,
            num_accumulations: 10,
        };
        assert!(test_template::<A, I>(&template_params, test_params)?);
        Ok(())
    }
}
