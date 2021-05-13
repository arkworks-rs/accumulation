#![cfg_attr(not(feature = "std"), no_std)]

//! A crate that provides infrastructure to implement accumulation schemes.
//! The interface for accumulation schemes were formalized in [\[BCMS20\]][\[BCMS20\]] and
//! [\[BCLMS20\]][bclms20].
//!
//! [\[BCMS20\]]: https://eprint.iacr.org/2020/499
//! [bclms20]: https://eprint.iacr.org/2020/1618

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
#![cfg_attr(docsrs, feature(doc_cfg))]

use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::CryptographicSponge;
use ark_std::rand::RngCore;

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
#[cfg_attr(docsrs, doc(cfg(feature = "r1cs")))]
pub mod constraints;

/// An accumulation scheme for the Hadamard product relation.
/// The construction is described in detail in [\[BCLMS20\]][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618
#[cfg(feature = "hp-as")]
#[cfg_attr(docsrs, doc(cfg(feature = "hp-as")))]
pub mod hp_as;

/// An accumulation scheme based on the hardness of the discrete log problem.
/// The construction is described in detail in [\[BCMS20\]][\[BCMS20\]].
///
/// [\[BCMS20\]]: https://eprint.iacr.org/2020/499
#[cfg(feature = "ipa-pc-as")]
#[cfg_attr(docsrs, doc(cfg(feature = "ipa-pc-as")))]
pub mod ipa_pc_as;

/// An accumulation scheme based on bilinear groups.
/// The construction is described in detail in [\[BCMS20\]][\[BCMS20\]].
///
/// [\[BCMS20\]]: https://eprint.iacr.org/2020/499
#[cfg(feature = "marlin-pc-as")]
#[cfg_attr(docsrs, doc(cfg(feature = "marlin-pc-as")))]
pub mod marlin_pc_as;

/// An accumulation scheme for a NARK for R1CS.
/// The construction is described in detail in [\[BCLMS20\]][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618
#[cfg(feature = "r1cs-nark-as")]
#[cfg_attr(docsrs, doc(cfg(feature = "r1cs-nark-as")))]
pub mod r1cs_nark_as;

/// An accumulation scheme for trivial homomorphic commitment schemes.
/// The construction is described in detail in [\[BCLMS20\]][bclms20].
///
/// [bclms20]: https://eprint.iacr.org/2020/1618
#[cfg(feature = "trivial-pc-as")]
#[cfg_attr(docsrs, doc(cfg(feature = "trivial-pc-as")))]
pub mod trivial_pc_as;

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// accumulates a stream of [`Inputs`][in] into an object called an [`Accumulator`][acc]. The prover
/// also outputs a [`Proof`][pf] attesting that the [`Accumulator`][acc] was computed correctly,
/// which a verifier can check. At any point, a decider can use an [`Accumulator`][acc] to determine
/// if each accumulated input satisfied the predicate.
/// The interface is defined in [\[BCLMS20\]][bclms20] as `SplitAccumulationScheme`.
///
/// [in]: Input
/// [acc]: Accumulator
/// [pf]: AccumulationScheme::Proof
/// [bclms20]: https://eprint.iacr.org/2020/1618
///
/// # Example
/// ```
/// // This example only serves to demonstrate the general flow of the trait.
///
/// use ark_accumulation::{AccumulationScheme, Accumulator, Input, MakeZK};
/// use ark_ff::PrimeField;
/// use ark_sponge::CryptographicSponge;
/// use ark_std::rand::RngCore;
///
/// // Basic setup to get the parameters and keys of an accumulation scheme.
/// fn initialize<
///     CF: PrimeField,
///     S: CryptographicSponge<CF>,
///     AS: AccumulationScheme<CF, S>,
///     R: RngCore,
/// >(
///     predicate_params: &AS::PredicateParams,
///     predicate_index: &AS::PredicateIndex,
///     rng: &mut R,
/// ) -> Result<(), AS::Error> {
///     let pp = AS::setup(rng)?;
///     let (prover_key, verifier_key, decider_key) =
///         AS::index(&pp, predicate_params, predicate_index)?;
///
/// #    unimplemented!()
/// }
///
/// // What happens if there is a new set of inputs?
/// fn step<
///     CF: PrimeField,
///     S: CryptographicSponge<CF>,
///     AS: AccumulationScheme<CF, S>,
///     R: RngCore,
/// >(
///     prover_key: AS::ProverKey,
///     verifier_key: AS::VerifierKey,
///     decider_key: AS::DeciderKey,
///
///     new_inputs: &Vec<Input<CF, S, AS>>,
///     old_accumulators: &mut Vec<Accumulator<CF, S, AS>>,
///     rng: &mut R,
/// ) -> Result<(), AS::Error> {
///     // If there is a new input, then...
///
///     // The prover may run:
///     let (accumulator, proof) = AS::prove(
///         &prover_key,
///         Input::<CF, S, AS>::map_to_refs(new_inputs),
///         Accumulator::<CF, S, AS>::map_to_refs(&*old_accumulators),
///         MakeZK::Enabled(rng),
///         None::<S>,
///     )?;
///
///     // After the accumulation, the verifier may run:
///     let verify_result = AS::verify(
///         &verifier_key,
///         Input::<CF, S, AS>::instances(new_inputs),
///         Accumulator::<CF, S, AS>::instances(&*old_accumulators),
///         &accumulator.instance,
///         &proof,
///         None::<S>,
///     )?;
///
///     // At any point, the decider may run:
///     let decide_result = AS::decide(&decider_key, accumulator.as_ref(), None::<S>)?;
///
/// #   unimplemented!()
/// }
pub trait AccumulationScheme<CF: PrimeField, S: CryptographicSponge<CF>>: Sized {
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
    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, CF, S, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, CF, S, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<CF, S, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
        S: 'a;

    /// Verifies that the new accumulator instance was computed properly from the input instances
    /// and old accumulator instances.
    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
        S: 'a;

    /// Determines whether an accumulator is valid, which means every accumulated input satisfies
    /// the predicate.
    fn decide<'a>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, CF, S, Self>,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a;
}

/// A special case of an [`AccumulationScheme`] that has empty witnesses, so entire
/// [`Inputs`][Input] and [`Accumulators`][Accumulator] are passed into the verifier.
/// The interface is defined in [\[BCMS20\]][\[BCMS20\]] as `AccumulationScheme` and in [\[BCLMS20\]][bclms20]
/// as `AtomicAccumulationScheme`.
///
/// [\[BCMS20\]]: https://eprint.iacr.org/2020/499
/// [bclms20]: https://eprint.iacr.org/2020/1618
pub trait AtomicAccumulationScheme<CF: PrimeField, S: CryptographicSponge<CF>>:
    AccumulationScheme<CF, S, InputWitness = (), AccumulatorWitness = ()>
{
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::{Accumulator, Input};
    use crate::{AccumulationScheme, MakeZK};
    use ark_ff::PrimeField;
    use ark_sponge::CryptographicSponge;
    use ark_std::marker::PhantomData;
    use ark_std::rand::RngCore;
    use ark_std::vec::Vec;

    pub const NUM_ITERATIONS: usize = 50;

    pub trait TestParameters {
        fn make_zk(&self) -> bool;
    }

    /// An interface for generating inputs and accumulators to test an accumulation scheme.
    pub trait ASTestInput<CF: PrimeField, S: CryptographicSponge<CF>, A: AccumulationScheme<CF, S>>
    {
        /// Parameters for setting up the test
        type TestParams: TestParameters;

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
        pub(crate) num_iterations: usize,
        pub(crate) num_inputs_per_iteration: Vec<usize>,
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
                        Input::<CF, S, AS>::map_to_refs(inputs),
                        Accumulator::<CF, S, AS>::map_to_refs(&old_accumulators),
                        if test_params.make_zk() {
                            MakeZK::Enabled(&mut rng)
                        } else {
                            MakeZK::Disabled
                        },
                        None::<S>,
                    )?;

                    if !AS::verify(
                        &vk,
                        Input::<CF, S, AS>::instances(inputs),
                        Accumulator::<CF, S, AS>::instances(&old_accumulators),
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

        /// Tests the initialization of the first accumulator using one input.
        pub fn single_input_init_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator using multiple inputs.
        pub fn multiple_inputs_init_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![3],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of one input and one accumulator.
        pub fn simple_accumulation_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 1],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of multiple inputs and multiple accumulators.
        pub fn multiple_inputs_accumulation_test(
            test_params: &I::TestParams,
        ) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 1, 2, 3],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of multiple accumulators without any inputs.
        pub fn accumulators_only_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 0, 0, 0],
            };

            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator without any inputs.
        pub fn no_inputs_init_test(test_params: &I::TestParams) -> Result<(), AS::Error> {
            let template_params = TemplateParams {
                num_iterations: 1,
                num_inputs_per_iteration: vec![0],
            };

            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }
    }
}
