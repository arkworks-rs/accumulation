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
    variant_size_differences
)]
#![forbid(unsafe_code)]

use rand_core::RngCore;

/// An interface for an accumulation scheme. In an accumulation scheme for a predicate, a prover
/// accumulates inputs and past accumulators into a new accumulator, which captures the properties
/// for ensuring every accumulated input satisfies the predicate. The prover additionally outputs a
/// proof that the accumulation was done correctly. Using the corresponding proof, a verifier can
/// check that the accumulator was computed properly. At any point, a decider can check an
/// accumulator to determine whether all of the accumulated inputs satisfy the predicate.
pub trait AccumulationScheme {
    /// The public parameters of the predicate.
    type PredicateParams;

    /// The index of the predicate.
    type PredicateIndex;

    /// The universal parameters for the accumulation scheme.
    type UniversalParams;

    /// The prover key, used to accumulate inputs and past accumulators and to prove that the
    /// accumulator was computed correctly .
    type ProverKey;

    /// The verifier key, used to check that the inputs and past accumulators were properly
    /// accumulated.
    type VerifierKey;

    /// The decider key, used to establish whether all of the accumulated inputs satisfy the
    /// predicate.
    type DeciderKey;

    /// The input to be accumulated.
    type Input;

    /// The accumulator, which represents accumulated inputs. It captures the essential properties
    /// for ensuring every accumulated input satisfies the predicate.
    type Accumulator;

    /// The proof, used to prove that the inputs and accumulators were accumulated properly.
    type Proof;

    /// The error used in the scheme.
    type Error;

    /// Outputs the universal parameters of the accumulation scheme.
    fn generate(rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error>;

    /// Outputs the prover, verifier, and decider keys specialized for a specific index of the
    /// predicate.
    fn index(
        universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error>;

    /// Accumulates the inputs and past accumulators. Additionally outputs the proof proving
    /// that the accumulation was computed properly.
    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = &'a Self::Input>,
        accumulators: impl IntoIterator<Item = &'a Self::Accumulator>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Accumulator, Self::Proof), Self::Error>
    where
        Self::Input: 'a,
        Self::Accumulator: 'a;

    /// Verifies using the proof that the inputs and past accumulators were properly accumulated.
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
