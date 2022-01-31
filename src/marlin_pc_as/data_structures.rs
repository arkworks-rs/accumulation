use ark_ec::PairingEngine;
use ark_ff::{to_bytes, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::marlin_pc::MarlinKZG10;
use ark_poly_commit::{kzg10, marlin_pc, LabeledCommitment, PolynomialCommitment, PolynomialLabel};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::{collect_sponge_bytes, collect_sponge_field_elements, Absorbable};
use ark_std::vec::Vec;

/// The [`PredicateIndex`][predicate_index] of the [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [predicate_index]: crate::AccumulationScheme::PredicateIndex
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
#[derive(Clone)]
pub struct PredicateIndex {
    /// The supported degree by the MarlinPC index.
    pub supported_degree: usize,

    /// The hiding bound supported by the MarlinPC index.
    pub supported_hiding_bound: usize,

    /// The degree bounds that are supported by the MarlinPC index.
    pub enforced_degree_bounds: Option<Vec<usize>>,
}

/// The [`ProverKey`][pk] of the [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [pk]: crate::AccumulationScheme::ProverKey
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
#[derive(Clone)]
pub struct ProverKey<E: PairingEngine> {
    /// The verifier key of MarlinPC.
    pub(crate) marlin_vk: marlin_pc::VerifierKey<E>,

    /// The power used to commit to randomness.
    pub(crate) beta_g: E::G1Affine,
}

/// An instance of the MarlinPC relation.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct MarlinPCInstance<E: PairingEngine> {
    /// The MarlinPC commitment to a polynomial.
    pub commitment: LabeledCommitment<marlin_pc::Commitment<E>>,

    /// Point where the proof was opened at.
    pub point: E::Fr,

    /// Evaluation of the committed polynomial at the point.
    pub evaluation: E::Fr,
}

impl<E: PairingEngine> Absorbable<E::Fq> for MarlinPCInstance<E>
where
    E::G1Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let degree_bound = self
            .commitment
            .degree_bound()
            .as_ref()
            .map(|d| to_bytes!(<E::Fq as From<u64>>::from(*d as u64)).unwrap());

        collect_sponge_bytes!(
            E::Fq,
            self.commitment.commitment(),
            degree_bound,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.evaluation).unwrap()
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fq> {
        let degree_bound = self
            .commitment
            .degree_bound()
            .as_ref()
            .map(|d| to_bytes!(<E::Fq as From<u64>>::from(*d as u64)).unwrap());

        collect_sponge_field_elements!(
            self.commitment.commitment(),
            degree_bound,
            to_bytes!(self.point).unwrap(),
            to_bytes!(self.evaluation).unwrap()
        )
    }
}

/// The [`InputInstance`][input_instance] of the [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [input_instance]: crate::AccumulationScheme::InputInstance
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct InputInstance<E: PairingEngine> {
    /// The MarlinPC instance.
    pub marlin_pc_instance: MarlinPCInstance<E>,

    /// The MarlinPC proof.
    pub marlin_pc_proof: <MarlinKZG10<E, DensePolynomial<E::Fr>> as PolynomialCommitment<
        E::Fr,
        DensePolynomial<E::Fr>,
    >>::Proof,
}

impl<E: PairingEngine> InputInstance<E> {
    pub(crate) fn zero() -> Self {
        let marlin_pc_commitment = LabeledCommitment::new(
            PolynomialLabel::new(),
            marlin_pc::Commitment::default(),
            None,
        );

        let marlin_pc_proof = kzg10::Proof::default();

        let marlin_pc_instance = MarlinPCInstance {
            commitment: marlin_pc_commitment,
            point: E::Fr::zero(),
            evaluation: E::Fr::zero(),
        };

        Self {
            marlin_pc_instance,
            marlin_pc_proof,
        }
    }
}

impl<E: PairingEngine> Absorbable<E::Fq> for InputInstance<E>
where
    E::G1Affine: Absorbable<E::Fq>,
    E::Fq: Absorbable<E::Fq>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(E::Fq, self.marlin_pc_instance, self.marlin_pc_proof)
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fq> {
        collect_sponge_field_elements!(self.marlin_pc_instance, self.marlin_pc_proof)
    }
}

/// The [`AccumulatorInstance`][acc_instance] of the [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [acc_instance]: crate::AccumulationScheme::AccumulatorInstance
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct AccumulatorInstance<E: PairingEngine> {
    /// The accumulated MarlinPC commitment.
    pub(crate) accumulated_commitment: E::G1Affine,

    /// The accumulated MarlinPC proof.
    pub(crate) accumulated_proof: E::G1Affine,
}

impl<E: PairingEngine> Absorbable<E::Fq> for AccumulatorInstance<E>
where
    E::G1Affine: Absorbable<E::Fq>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(E::Fq, self.accumulated_commitment, self.accumulated_proof)
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fq> {
        collect_sponge_field_elements!(self.accumulated_commitment, self.accumulated_proof)
    }
}

/// The randomness used to apply zero-knowledge to the accumulated commitment and proof.
/// If used, the randomness is the  [`Proof`][proof] of the
/// [`AtomicASForMarlinPC`][as_for_marlin_pc].
///
/// [Proof]: crate::AccumulationScheme::Proof
/// [as_for_marlin_pc]: crate::marlin_pc_as::AtomicASForMarlinPC
#[derive(Clone, PartialEq, Eq)]
pub struct Randomness<E: PairingEngine> {
    /// The randomness used to blind the accumulated commitment.
    pub(crate) accumulated_commitment_randomness: E::G1Affine,

    /// The randomness used to blind the accumulated proof.
    pub(crate) accumulated_proof_randomness: E::G1Affine,
}

impl<E: PairingEngine> Absorbable<E::Fq> for Randomness<E>
where
    E::G1Affine: Absorbable<E::Fq>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        collect_sponge_bytes!(
            E::Fq,
            self.accumulated_commitment_randomness,
            self.accumulated_proof_randomness
        )
    }

    fn to_sponge_field_elements(&self) -> Vec<<E as PairingEngine>::Fq> {
        collect_sponge_field_elements!(
            self.accumulated_commitment_randomness,
            self.accumulated_proof_randomness
        )
    }
}
