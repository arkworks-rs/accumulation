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

use rand_core::RngCore;

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc as std;

/// Common errors for `AccumulationScheme`.
pub mod error;

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// accumulates a stream of inputs into a single accumulator, which holds the necessary properties
/// to ensure each accumulated input satisfies the predicate. The prover also outputs a proof
/// attesting that the accumulator was computed correctly, which a verifier can check. At any
/// point, a decider use an accumulator to determine if each accumulated input satisfies the
/// predicate.
pub trait AccumulationScheme {
    /// The public parameters of the accumulation scheme's predicate.
    type PredicateParams;

    /// The index of the accumulation scheme's predicate.
    type PredicateIndex;

    /// The universal parameters for the accumulation scheme.
    type UniversalParams;

    /// The prover key, used to accumulate inputs and past accumulators and to prove that the
    /// new accumulator was computed correctly from the inputs and old accumulators.
    type ProverKey;

    /// The verifier key, used to check that an accumulator was computed correctly from the inputs
    /// and old accumulators.
    type VerifierKey;

    /// The decider key, used to establish whether each of the accumulated inputs satisfes the
    /// predicate.
    type DeciderKey;

    /// The input to be accumulated.
    type Input;

    /// The accumulator, which captures the essential properties of the accumulated inputs for
    /// ensuring each satisfies the predicate.
    type Accumulator;

    /// The proof, used to prove that the accumulator was properly computed.
    type Proof;

    /// The error type used in the scheme.
    type Error;

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
        inputs: impl IntoIterator<Item = &'a Self::Input>,
        accumulators: impl IntoIterator<Item = &'a Self::Accumulator>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Accumulator, Self::Proof), Self::Error>
    where
        Self::Input: 'a,
        Self::Accumulator: 'a;

    /// Verifies using a proof that the new accumulator was computed properly from the inputs and
    /// old accumulators.
    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        inputs: impl IntoIterator<Item = &'a Self::Input>,
        accumulators: impl IntoIterator<Item = &'a Self::Accumulator>,
        new_accumulator: &Self::Accumulator,
        proof: &Self::Proof,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<bool, Self::Error>
    where
        Self::Input: 'a,
        Self::Accumulator: 'a;

    /// Determines whether an accumulator is valid, which means every accumulated input satisfies
    /// the predicate.
    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: &Self::Accumulator,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<bool, Self::Error>;
}

#[cfg(test)]
pub mod tests {
    use crate::std::vec::Vec;
    use rand_core::RngCore;

    use crate::AccumulationScheme;

    /// An interface for generating inputs and accumulators to test an accumulation scheme.
    pub trait AccumulationSchemeTestInput<A: AccumulationScheme> {
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
        ) -> Vec<A::Accumulator>;

        /// Generates `num_inputs` inputs for one accumulation.
        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<A::Input>;
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
    pub fn test_template<A: AccumulationScheme, I: AccumulationSchemeTestInput<A>>(
        template_params: &TemplateParams,
        test_params: &I::TestParams,
    ) -> Result<bool, A::Error> {
        assert!(template_params.num_iterations > 0);

        let mut rng = algebra_core::test_rng();
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
                    &inputs,
                    &old_accumulators,
                    &accumulator,
                    &proof,
                    Some(&mut rng),
                )? {
                    println!("{}", format!("Verify failed on accumulation {}", i));
                    return Ok(false);
                }

                old_accumulators.push(accumulator);
            }

            assert!(old_accumulators.len() > 0);
            if !A::decide(&dk, old_accumulators.last().unwrap(), Some(&mut rng))? {
                println!("Decide failed");
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn no_starting_accumulators_test<
        A: AccumulationScheme,
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

    pub fn no_inputs_test<A: AccumulationScheme, I: AccumulationSchemeTestInput<A>>(
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

    pub fn base_test<A: AccumulationScheme, I: AccumulationSchemeTestInput<A>>(
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
        A: AccumulationScheme,
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

    pub fn multiple_inputs_test<A: AccumulationScheme, I: AccumulationSchemeTestInput<A>>(
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

    pub fn multiple_accumulations_test<A: AccumulationScheme, I: AccumulationSchemeTestInput<A>>(
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
        A: AccumulationScheme,
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
        A: AccumulationScheme,
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
