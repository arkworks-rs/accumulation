#![cfg_attr(not(feature = "std"), no_std)]

//! A crate for accumulation schemes.
#![warn(
    const_err,
    future_incompatible,
    // missing_docs,
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

use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::CryptographicSponge;
use rand_core::RngCore;

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate bench_utils;

extern crate ark_std as std;

mod data_structures;
/// Common data structures used by `AccumulationScheme`.
pub use data_structures::*;

/// Common errors for `AidedAccumulationScheme`.
pub mod error;

#[cfg(feature = "r1cs")]
pub mod constraints;

pub mod hc_as;

pub mod hp_as;

/// An accumulation scheme based on the hardness of the discrete log problem.
/// The construction for the accumulation scheme is taken from [[BCMS20]][pcdas].
///
/// [pcdas]: https://eprint.iacr.org/2020/499
pub mod ipa_as;

pub mod nark_as;

pub enum MakeZK<'a> {
    /// Always enable zero-knowledge accumulation if available.
    Enabled(&'a mut dyn RngCore),

    /// Enable zero-knowledge accumulation if any input or accumulator requires zero-knowledge.
    Inherited(Option<&'a mut dyn RngCore>),
}

impl<'a> MakeZK<'a> {
    fn into_components<F: Fn() -> bool>(
        self,
        inherit_zk: F,
    ) -> (bool, Option<&'a mut dyn RngCore>) {
        match self {
            MakeZK::Enabled(rng) => (true, Some(rng)),
            MakeZK::Inherited(rng) => (inherit_zk(), rng),
        }
    }
}

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// to ensure each accumulated input satisfies the predicate. The prover also outputs a proof
/// attesting that the accumulator was computed correctly, which a verifier can check. At any
/// point, a decider use an accumulator to determine if each accumulated input satisfies the
/// predicate.
/// Accumulation schemes are aided accumulation schemes with empty witnesses. So, verifiers receive
/// entire accumulators and inputs.
pub trait AtomicAccumulationScheme<CF: PrimeField, S: CryptographicSponge<CF>>:
    AccumulationScheme<CF, S, InputWitness = (), AccumulatorWitness = ()>
{
}

/// An interface for an aided accumulation scheme. In an aided accumulation scheme, accumulators
/// and inputs are split into instance, witness pairs. Verifiers no longer receive entire
/// accumulators or inputs but instead receive their respective instances.
pub trait AccumulationScheme<CF: PrimeField, S: CryptographicSponge<CF>>: Sized {
    /// The universal parameters for the accumulation scheme.
    type UniversalParams: Clone;

    /// The public parameters of the accumulation scheme's predicate.
    type PredicateParams: Clone;

    /// The index of the accumulation scheme's predicate.
    type PredicateIndex: Clone;

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
    type InputInstance: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The witness of the input to be accumulated.
    type InputWitness: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The instance of the accumulator.
    type AccumulatorInstance: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The witness of the accumulator.
    type AccumulatorWitness: Clone + CanonicalSerialize + CanonicalDeserialize;

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
    fn prove_with_sponge<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, CF, S, Self>>,
        accumulators: impl IntoIterator<Item = AccumulatorRef<'a, CF, S, Self>>,
        make_zk: MakeZK<'_>,
        sponge: S,
    ) -> Result<(Accumulator<CF, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a;

    /// Accumulates the inputs and past accumulators. Additionally outputs the proof attesting
    /// that that the new accumulator was computed properly from the inputs and old accumulators.
    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, CF, S, Self>>,
        accumulators: impl IntoIterator<Item = AccumulatorRef<'a, CF, S, Self>>,
        make_zk: MakeZK<'_>,
    ) -> Result<(Accumulator<CF, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        Self::prove_with_sponge(prover_key, inputs, accumulators, make_zk, S::new())
    }

    /// Verifies using a proof that the new accumulator instance was computed properly from the
    /// input instances and old accumulator instances.
    fn verify_with_sponge<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: S,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a;

    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a,
    {
        Self::verify_with_sponge(
            verifier_key,
            input_instances,
            accumulator_instances,
            new_accumulator_instance,
            proof,
            S::new(),
        )
    }

    /// Determines whether an accumulator is valid, which means every accumulated input satisfies
    /// the predicate.
    fn decide_with_sponge<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, CF, S, Self>,
        sponge: S,
    ) -> Result<bool, Self::Error>;

    fn decide<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, CF, S, Self>,
    ) -> Result<bool, Self::Error> {
        Self::decide_with_sponge(decider_key, accumulator, S::new())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::{Accumulator, Input};
    use crate::std::vec::Vec;
    use crate::{AccumulationScheme, MakeZK};
    use ark_ff::PrimeField;
    use ark_sponge::CryptographicSponge;
    use rand_core::RngCore;
    use std::marker::PhantomData;

    pub const NUM_ITERATIONS: usize = 1;

    /// An interface for generating inputs and accumulators to test an accumulation scheme.
    pub trait ASTestInput<CF: PrimeField, S: CryptographicSponge<CF>, A: AccumulationScheme<CF, S>>
    {
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

        /// Generates `num_inputs` inputs for one accumulation.
        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<CF, S, A>>;
    }

    pub struct TemplateParams {
        num_iterations: usize,
        num_inputs_per_iteration: Vec<usize>,
    }

    pub struct ASTests<CF, S, AS, I>
    where
        CF: PrimeField,
        S: CryptographicSponge<CF>,
        AS: AccumulationScheme<CF, S>,
        I: ASTestInput<CF, S, AS>,
    {
        _constraint_field: PhantomData<CF>,
        _sponge: PhantomData<S>,
        _acc_scheme: PhantomData<AS>,
        _test_input: PhantomData<I>,
    }

    impl<CF, S, AS, I> ASTests<CF, S, AS, I>
    where
        CF: PrimeField,
        S: CryptographicSponge<CF>,
        AS: AccumulationScheme<CF, S>,
        I: ASTestInput<CF, S, AS>,
    {
        /// For each iteration, runs the accumulation scheme for `num_accumulations` steps of proving
        /// and verifying.
        /// At the end of the iteration, the last accumulator is put through a single decider.
        /// The function will return whether all of the verifiers and deciders returned true
        /// from all of the iterations.
        pub fn test_template(
            template_params: &TemplateParams,
            test_params: &I::TestParams,
        ) -> Result<bool, AS::Error> {
            assert!(template_params.num_iterations > 0);
            let num_inputs_per_iteration = &template_params.num_inputs_per_iteration;
            let num_iterations = template_params.num_iterations;
            let total_num_inputs = num_iterations * num_inputs_per_iteration.iter().sum::<usize>();

            let mut rng = ark_std::test_rng();
            let universal_params = AS::generate(&mut rng)?;

            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let (pk, vk, dk) = AS::index(&universal_params, &predicate_params, &predicate_index)?;

            let inputs = I::generate_inputs(&input_params, total_num_inputs, &mut rng);
            assert_eq!(total_num_inputs, inputs.len());
            let mut inputs_start = 0;

            for _ in 0..num_iterations {
                let mut old_accumulators = Vec::with_capacity(num_inputs_per_iteration.len());
                for num_inputs in num_inputs_per_iteration {
                    let inputs = &inputs[inputs_start..(inputs_start + num_inputs)];
                    inputs_start += num_inputs;

                    let (accumulator, proof) = AS::prove(
                        &pk,
                        Input::<CF, S, AS>::map_to_refs(inputs),
                        Accumulator::<CF, S, AS>::map_to_refs(&old_accumulators),
                        MakeZK::Inherited(Some(&mut rng)),
                    )?;

                    if !AS::verify(
                        &vk,
                        Input::<CF, S, AS>::instances(inputs),
                        Accumulator::<CF, S, AS>::instances(&old_accumulators),
                        &accumulator.instance,
                        &proof,
                    )? {
                        println!("{}", format!("Verify failed"));
                        return Ok(false);
                    }

                    old_accumulators.push(accumulator);
                }

                assert!(old_accumulators.len() > 0);
                if !AS::decide(&dk, old_accumulators.last().unwrap().as_ref())? {
                    println!("Decide failed");
                    return Ok(false);
                }
            }

            Ok(true)
        }

        pub fn single_input_initialization_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        pub fn multiple_inputs_initialization_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![2],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        pub fn simple_accumulation_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1; 2],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        pub fn multiple_accumulations_multiple_inputs_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![5; 5],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        // Only add this test if scheme is intended to support cases with accumulators but no inputs
        pub fn accumulators_only_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let mut num_inputs_per_iteration = vec![0; 3];

            // To initialize the starting accumulator
            num_inputs_per_iteration[0] = 1;

            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration,
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        // Only add this test if scheme is intended to support cases with no accumulators or inputs
        pub fn no_accumulators_or_inputs_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![0; 3],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }
    }
}
