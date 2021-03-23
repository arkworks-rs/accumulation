//! A crate that provides infrastructure to implement accumulation schemes.
//! The interface for accumulation schemes were formalized in [BCMS20][bcms20] and
//! [BCLMS20][bclms20].
//!
//! [bcms20]: https://eprint.iacr.org/2020/499.pdf
//! [bclms20]: https://eprint.iacr.org/2020/1618.pdf

#![warn(
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

use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::CryptographicSponge;
use rand_core::RngCore;

#[macro_use]
extern crate derivative;

#[cfg(feature = "r1cs-nark-as")]
#[macro_use]
extern crate ark_std;

/// Common data structures used by [`AccumulationScheme`].
pub use data_structures::*;
mod data_structures;

/// Common errors for [`AccumulationScheme`].
pub mod error;

/// Traits for [`AccumulationScheme`] verifier gadgets.
#[cfg(feature = "r1cs")]
pub mod constraints;

/// An accumulation scheme for the Hadamard product relation.
/// The construction is described in detail in [BCLMS20][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
#[cfg(feature = "hp-as")]
pub mod hp_as;

/// An accumulation scheme based on the hardness of the discrete log problem.
/// The construction is described in detail in [BCMS20][bcms20].
///
/// [bcms20]: https://eprint.iacr.org/2020/499
#[cfg(feature = "ipa-pc-as")]
pub mod ipa_pc_as;

/// An accumulation scheme for a NARK for R1CS.
/// The construction is described in detail in [BCLMS20][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
#[cfg(feature = "r1cs-nark-as")]
pub mod r1cs_nark_as;

/// An accumulation scheme for trivial homomorphic commitment schemes.
/// The construction is described in detail in [BCLMS20][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
#[cfg(feature = "trivial-pc-as")]
pub mod trivial_pc_as;

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// accumulates a stream of [`Inputs`][in] into an object called an [`Accumulator`][acc]. The prover
/// also outputs a [`Proof`][pf] attesting that the [`Accumulator`][acc] was computed correctly,
/// which a verifier can check. At any point, a decider can use an [`Accumulator`][acc] to determine
/// if each accumulated input satisfied the predicate.
/// The interface is defined in [BCLMS20][bclms20] as `SplitAccumulationScheme`.
///
/// [in]: Input
/// [acc]: Accumulator
/// [pf]: AccumulationScheme::Proof
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
pub trait AccumulationScheme<CF: PrimeField>: Sized {
    /// The public parameters for the accumulation scheme.
    type PublicParameters: Clone;

    /// The public parameters of the accumulation scheme's predicate.
    type PredicateParams: Clone;

    /// The index of the accumulation scheme's predicate.
    type PredicateIndex: Clone;

    /// The key used to accumulate inputs and old accumulators and to prove that the accumulation
    /// was computed correctly.
    type ProverKey: Clone;

    /// The key used to check that an accumulator was computed correctly from the inputs
    /// and old accumulators.
    type VerifierKey: Clone;

    /// The key used to establish whether each of the accumulated inputs satisfies the predicate.
    type DeciderKey: Clone;

    /// The instance of the input to be accumulated.
    type InputInstance: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The witness of the input to be accumulated.
    type InputWitness: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The instance of the accumulator.
    type AccumulatorInstance: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The witness of the accumulator.
    type AccumulatorWitness: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The proof attesting that an accumulator was properly computed.
    type Proof: Clone;

    /// The error type used in the scheme.
    type Error: ark_std::error::Error;

    /// Outputs the public parameters of the accumulation scheme.
    fn setup(rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error>;

    /// Outputs the prover, verifier, and decider keys, specialized for a specific index of the
    /// predicate.
    fn index(
        public_params: &Self::PublicParameters,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error>;

    /// Accumulates inputs and past accumulators. Additionally outputs a proof attesting that the
    /// new accumulator was computed properly from the inputs and old accumulators.
    fn prove<'a, S: CryptographicSponge<CF>>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, CF, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, CF, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<CF, Self>, Self::Proof), Self::Error>
    where
        Self: 'a;

    /// Verifies that the new accumulator instance was computed properly from the input instances
    /// and old accumulator instances.
    fn verify<'a, S: CryptographicSponge<CF>>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a;

    /// Determines whether an accumulator is valid, which means every accumulated input satisfies
    /// the predicate.
    fn decide<'a, S: CryptographicSponge<CF>>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, CF, Self>,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a;
}

/// A special case of an [`AccumulationScheme`] that has empty witnesses, so entire
/// [`Inputs`][Input] and [`Accumulators`][Accumulator] are passed into the verifier.
/// The interface is defined in [BCMS20][bcms20] as `AccumulationScheme` and in [BCLMS20][bclms20]
/// as `AtomicAccumulationScheme`.
///
/// [bcms20]: https://eprint.iacr.org/2020/499.pdf
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
pub trait AtomicAccumulationScheme<CF: PrimeField>:
    AccumulationScheme<CF, InputWitness = (), AccumulatorWitness = ()>
{
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::{Accumulator, Input};
    use crate::{AccumulationScheme, MakeZK};
    use ark_ff::PrimeField;
    use ark_sponge::CryptographicSponge;
    use ark_std::marker::PhantomData;
    use ark_std::vec::Vec;
    use rand_core::RngCore;

    pub const NUM_ITERATIONS: usize = 50;

    /// An interface for generating inputs and accumulators to test an accumulation scheme.
    pub trait ASTestInput<CF: PrimeField, A: AccumulationScheme<CF>> {
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
        ) -> Vec<Input<CF, A>>;
    }

    pub struct TemplateParams {
        num_iterations: usize,
        num_inputs_per_iteration: Vec<usize>,
    }

    pub struct ASTests<CF, AS, I, S>
    where
        CF: PrimeField,
        AS: AccumulationScheme<CF>,
        I: ASTestInput<CF, AS>,
        S: CryptographicSponge<CF>,
    {
        _constraint_field: PhantomData<CF>,
        _sponge: PhantomData<S>,
        _acc_scheme: PhantomData<AS>,
        _test_input: PhantomData<I>,
    }

    impl<CF, AS, I, S> ASTests<CF, AS, I, S>
    where
        CF: PrimeField,
        AS: AccumulationScheme<CF>,
        I: ASTestInput<CF, AS>,
        S: CryptographicSponge<CF>,
    {
        /// For each iteration, runs the accumulation scheme for `num_accumulations` steps of
        /// proving and verifying.
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
            let public_params = AS::setup(&mut rng)?;

            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let (pk, vk, dk) = AS::index(&public_params, &predicate_params, &predicate_index)?;

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
                        Input::<CF, AS>::map_to_refs(inputs),
                        Accumulator::<CF, AS>::map_to_refs(&old_accumulators),
                        MakeZK::Inherited(Some(&mut rng)),
                        None::<S>,
                    )?;

                    if !AS::verify(
                        &vk,
                        Input::<CF, AS>::instances(inputs),
                        Accumulator::<CF, AS>::instances(&old_accumulators),
                        &accumulator.instance,
                        &proof,
                        None::<S>,
                    )? {
                        println!("{}", format!("Verify failed"));
                        return Ok(false);
                    }

                    old_accumulators.push(accumulator);
                }

                assert!(old_accumulators.len() > 0);
                if !AS::decide(&dk, old_accumulators.last().unwrap().as_ref(), None::<S>)? {
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

        pub fn no_accumulators_or_inputs_fail_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: 1,
                num_inputs_per_iteration: vec![0],
            };

            assert!(Self::test_template(&template_params, test_params).is_err());
            Ok(())
        }
    }
}
