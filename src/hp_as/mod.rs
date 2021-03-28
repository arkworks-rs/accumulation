use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::ASError::{MalformedAccumulator, MalformedInput};
use crate::error::{ASError, BoxedError};
use crate::ConstraintF;
use crate::{AccumulationScheme, MakeZK};

use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{One, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::trivial_pc::{CommitterKey as PedersenCommitmentCK, PedersenCommitment};
use ark_poly_commit::UVPolynomial;
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;
use ark_std::UniformRand;
use rand_core::RngCore;

mod data_structures;
pub use data_structures::*;

/// The verifier constraints of [`ASForHadamardProducts`].
#[cfg(feature = "r1cs")]
pub mod constraints;

/// An accumulation scheme for the Hadamard product relation.
/// The construction is described in detail in [BCLMS20][bclms20].
///
/// The implementation substitutes power challenges with multiple independent challenges when
/// possible to lower constraint costs for the verifier.
/// See Remark 10.1 in [BCLMS20][bclms20] for more details.
///
/// [bclms20]: https://eprint.iacr.org/2020/1618.pdf
pub struct ASForHadamardProducts<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
}

impl<G> ASForHadamardProducts<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    fn check_input_witness_structure<'a>(
        witness: &'a InputWitness<G::ScalarField>,
        prover_key: &'a PedersenCommitmentCK<G>,
        vec_len: usize,
        is_accumulator: bool,
    ) -> Result<&'a InputWitness<G::ScalarField>, BoxedError> {
        // The a and b vectors of the relation must not be empty.
        if witness.a_vec.len() == 0 || witness.b_vec.len() == 0 {
            let message =
                "A vector of the Hadamard Product relation with a length of 0 is unsupported."
                    .to_string();
            return Err(BoxedError::new(if is_accumulator {
                MalformedAccumulator(message)
            } else {
                MalformedInput(message)
            }));
        }

        // The number of elements of the a and b vectors must be supported by the prover key.
        if witness.a_vec.len() > prover_key.supported_num_elems()
            || witness.b_vec.len() > prover_key.supported_num_elems()
        {
            let message =
                "A vector of the Hadamard Product relation has a length that exceeds the prover \
                key's supported length."
                    .to_string();
            return Err(BoxedError::new(if is_accumulator {
                MalformedAccumulator(message)
            } else {
                MalformedInput(message)
            }));
        }

        // All a and b vectors of the witnesses to be accumulated must have equal lengths.
        if witness.a_vec.len() != witness.b_vec.len() || witness.a_vec.len() != vec_len {
            let message =
                "All of the vectors of the Hadamard Product relation that have or will be \
                accumulated must have equal lengths"
                    .to_string();
            return Err(BoxedError::new(if is_accumulator {
                MalformedAccumulator(message)
            } else {
                MalformedInput(message)
            }));
        }

        Ok(witness)
    }

    fn check_proof_structure(proof: &Proof<G>, num_inputs: usize) -> bool {
        assert!(num_inputs > 0);

        // The number of commitments to the low and high coefficients must be equal, given how
        // they were computed.
        if proof.t_comms.low.len() != proof.t_comms.high.len() {
            return false;
        }

        let placeholder_input = if proof.hiding_comms.is_some() && num_inputs == 1 {
            1
        } else {
            0
        };

        // The number of commitments can be derived from the number of inputs and the hiding
        // requirements. Ensure that they match.
        if proof.t_comms.low.len() != num_inputs - 1 + placeholder_input {
            return false;
        }

        true
    }

    fn squeeze_mu_challenges(
        sponge: &mut impl CryptographicSponge<ConstraintF<G>>,
        num_inputs: usize,
        make_zk: bool,
    ) -> Vec<G::ScalarField> {
        let mut mu_challenges = Vec::with_capacity(num_inputs);
        mu_challenges.push(G::ScalarField::one());

        if num_inputs > 1 {
            let mu_size = FieldElementSize::Truncated(128);
            mu_challenges.append(&mut sponge.squeeze_nonnative_field_elements_with_sizes(
                vec![mu_size; num_inputs - 1].as_slice(),
            ));
        }

        if make_zk {
            mu_challenges.push(mu_challenges[1].mul(mu_challenges[num_inputs - 1]));
        }

        mu_challenges
    }

    fn squeeze_nu_challenges(
        sponge: &mut impl CryptographicSponge<ConstraintF<G>>,
        num_inputs: usize,
    ) -> Vec<G::ScalarField> {
        let nu_size = FieldElementSize::Truncated(128);
        let nu_challenge: G::ScalarField = sponge
            .squeeze_nonnative_field_elements_with_sizes(vec![nu_size].as_slice())
            .pop()
            .unwrap();

        let mut nu_challenges = Vec::with_capacity(2 * num_inputs - 1);
        let mut cur_nu_challenge = G::ScalarField::one();

        for _ in 0..(2 * num_inputs - 1) {
            nu_challenges.push(cur_nu_challenge);
            cur_nu_challenge *= &nu_challenge;
        }

        nu_challenges
    }

    fn compute_hp(a_vec: &[G::ScalarField], b_vec: &[G::ScalarField]) -> Vec<G::ScalarField> {
        let mut product = Vec::with_capacity(a_vec.len().min(b_vec.len()));
        for (a, b) in a_vec.iter().zip(b_vec.iter()) {
            product.push(a.clone() * b);
        }

        product
    }

    // Assumes the length of a_vec and b_vec is hp_vec_len or below.
    fn compute_t_vecs(
        input_witnesses: &[&InputWitness<G::ScalarField>],
        mu_challenges: &[G::ScalarField],
        hp_vec_len: usize,
        hiding_vecs: Option<&(Vec<G::ScalarField>, Vec<G::ScalarField>)>,
    ) -> Vec<Vec<G::ScalarField>> {
        let num_inputs = input_witnesses.len();
        assert!(num_inputs + if hiding_vecs.is_some() { 1 } else { 0 } <= mu_challenges.len());

        let mut t_vecs = vec![Vec::with_capacity(hp_vec_len); 2 * num_inputs - 1];
        for li in 0..hp_vec_len {
            let mut a_coeffs = Vec::with_capacity(num_inputs);
            let mut b_coeffs = Vec::with_capacity(num_inputs);

            for (ni, input_witness) in input_witnesses.iter().enumerate() {
                a_coeffs.push(
                    input_witness
                        .a_vec
                        .get(li)
                        .map(|a| mu_challenges[ni].clone().mul(a))
                        .unwrap_or(G::ScalarField::zero()),
                );

                b_coeffs.push(
                    input_witness
                        .b_vec
                        .get(li)
                        .map(G::ScalarField::clone)
                        .unwrap_or(G::ScalarField::zero()),
                );
            }

            b_coeffs.reverse();

            if let Some((hiding_a, hiding_b)) = hiding_vecs {
                if li < hiding_a.len() {
                    a_coeffs[0] += hiding_a[li].mul(&mu_challenges[num_inputs]);
                }

                if li < hiding_b.len() {
                    b_coeffs[0] += hiding_b[li].mul(&mu_challenges[1]);
                }
            }

            let a_poly = DensePolynomial::from_coefficients_vec(a_coeffs);
            let b_poly = DensePolynomial::from_coefficients_vec(b_coeffs);

            let product_polynomial = a_poly.naive_mul(&b_poly);
            let mut product_polynomial_coeffs = product_polynomial.coeffs;

            if product_polynomial_coeffs.len() < 2 * num_inputs - 1 {
                product_polynomial_coeffs
                    .resize_with(2 * num_inputs - 1, || G::ScalarField::zero());
            }

            for i in 0..(2 * num_inputs - 1) {
                t_vecs[i].push(product_polynomial_coeffs[i].clone());
            }
        }

        t_vecs
    }

    /// Outputs commitments and randomizers to each t_vec, excluding the `n-1`th t_vec
    /// The commitments and randomizers are split into two, one computed on everything
    /// before the `n-1`th t_vec and one computed on everything after the `n-1`th t_vec.
    fn compute_t_comms(
        ck: &PedersenCommitmentCK<G>,
        t_vecs: &Vec<Vec<G::ScalarField>>,
    ) -> Result<ProofTCommitments<G>, BoxedError> {
        if t_vecs.len() == 0 {
            return Ok(ProofTCommitments {
                low: vec![],
                high: vec![],
            });
        }

        let num_inputs = (t_vecs.len() + 1) / 2;

        let mut t_comms = ProofTCommitments {
            low: Vec::with_capacity(num_inputs - 1),
            high: Vec::with_capacity(num_inputs - 1),
        };

        for (i, t_vec) in t_vecs.iter().enumerate() {
            if i == num_inputs - 1 {
                continue;
            }

            let comm = PedersenCommitment::commit(ck, t_vec.as_slice(), None);

            (if i < num_inputs - 1 {
                &mut t_comms.low
            } else {
                &mut t_comms.high
            })
            .push(comm);
        }

        Ok(t_comms)
    }

    pub(crate) fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a G>,
        challenges: &[G::ScalarField],
        hiding_comms: Option<&G::Projective>,
    ) -> G::Projective {
        let mut combined_commitment = G::Projective::zero();
        for (i, commitment) in commitments.into_iter().enumerate() {
            combined_commitment += &commitment.mul(challenges[i].into());
        }

        if let Some(hiding_comms) = hiding_comms {
            combined_commitment += hiding_comms;
        }

        combined_commitment
    }

    fn compute_combined_hp_commitments(
        input_instances: &[&InputInstance<G>],
        proof: &Proof<G>,
        mu_challenges: &[G::ScalarField],
        nu_challenges: &[G::ScalarField],
        combined_challenges: &[G::ScalarField],
    ) -> InputInstance<G> {
        let num_inputs = input_instances.len();

        let hiding_comm_addend_1 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| hiding_comms.comm_1.mul(mu_challenges[num_inputs].into()));

        let combined_comm_1 = Self::combine_commitments(
            input_instances.iter().map(|instance| &instance.comm_1),
            combined_challenges,
            hiding_comm_addend_1.as_ref(),
        );

        let hiding_comm_addend_2 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| hiding_comms.comm_2.mul(mu_challenges[1].into()));

        let combined_comm_2 = Self::combine_commitments(
            input_instances
                .iter()
                .map(|instance| &instance.comm_2)
                .rev(),
            nu_challenges,
            hiding_comm_addend_2.as_ref(),
        );

        let combined_comm_3 = {
            let t_comm_low_addend =
                Self::combine_commitments(proof.t_comms.low.iter(), &nu_challenges, None);

            let t_comm_high_addend = Self::combine_commitments(
                proof.t_comms.high.iter(),
                &nu_challenges[num_inputs..],
                None,
            );

            let hiding_comm_addend_3 = proof
                .hiding_comms
                .as_ref()
                .map(|hiding_comms| hiding_comms.comm_3.mul(mu_challenges[num_inputs].into()));

            let comm_3_addend = Self::combine_commitments(
                input_instances.iter().map(|instance| &instance.comm_3),
                &mu_challenges,
                hiding_comm_addend_3.as_ref(),
            )
            .mul(nu_challenges[num_inputs - 1].into());

            t_comm_low_addend + &t_comm_high_addend + &comm_3_addend
        };

        let mut combined_comms = G::Projective::batch_normalization_into_affine(&[
            combined_comm_3,
            combined_comm_2,
            combined_comm_1,
        ]);

        InputInstance {
            comm_1: combined_comms.pop().unwrap(),
            comm_2: combined_comms.pop().unwrap(),
            comm_3: combined_comms.pop().unwrap(),
        }
    }

    fn scale_vector(vector: &Vec<G::ScalarField>, coeff: &G::ScalarField) -> Vec<G::ScalarField> {
        let mut output = Vec::with_capacity(vector.len());
        for f in vector {
            output.push(f.mul(coeff));
        }

        output
    }

    pub(crate) fn combine_vectors<'a>(
        vectors: impl IntoIterator<Item = &'a Vec<G::ScalarField>>,
        challenges: &[G::ScalarField],
        hiding_vecs: Option<&Vec<G::ScalarField>>,
    ) -> Vec<G::ScalarField> {
        let mut output = hiding_vecs
            .map(|hiding_vecs| hiding_vecs.clone())
            .unwrap_or(Vec::new());
        for (ni, vector) in vectors.into_iter().enumerate() {
            for (li, elem) in vector.into_iter().enumerate() {
                let product = challenges[ni].mul(elem);
                if li >= output.len() {
                    output.push(product);
                } else {
                    output[li] += &product;
                }
            }
        }

        output
    }

    pub(crate) fn combine_randomness<'a>(
        randomness: impl IntoIterator<Item = Option<&'a G::ScalarField>>,
        challenges: &[G::ScalarField],
        hiding_rands: Option<&G::ScalarField>,
    ) -> G::ScalarField {
        let mut combined_randomness = G::ScalarField::zero();
        for (i, rand) in randomness.into_iter().enumerate() {
            if rand.is_some() {
                combined_randomness += &rand.unwrap().mul(challenges[i].clone());
            }
        }

        if let Some(hiding_rands) = hiding_rands {
            combined_randomness += hiding_rands;
        }

        combined_randomness
    }

    fn compute_combined_hp_openings(
        input_witnesses: &[&InputWitness<G::ScalarField>],
        mu_challenges: &[G::ScalarField],
        nu_challenges: &[G::ScalarField],
        combined_challenges: &[G::ScalarField],
        hiding_vecs: Option<&(Vec<G::ScalarField>, Vec<G::ScalarField>)>,
        hiding_rands: Option<&InputWitnessRandomness<G::ScalarField>>,
    ) -> InputWitness<G::ScalarField> {
        let num_inputs = input_witnesses.len();

        let hiding_vec_addend_1 = hiding_vecs
            .map(|hiding_vecs| Self::scale_vector(&hiding_vecs.0, &mu_challenges[num_inputs]));

        let a_opening_vec = Self::combine_vectors(
            input_witnesses.iter().map(|witness| &witness.a_vec),
            combined_challenges,
            hiding_vec_addend_1.as_ref(),
        );

        let hiding_vec_addend_2 =
            hiding_vecs.map(|hiding_vecs| Self::scale_vector(&hiding_vecs.1, &mu_challenges[1]));

        let b_opening_vec = Self::combine_vectors(
            input_witnesses.iter().map(|witness| &witness.b_vec).rev(),
            nu_challenges,
            hiding_vec_addend_2.as_ref(),
        );

        let randomness = if let Some(hiding_rands) = hiding_rands {
            let hiding_rand_addend_1 = hiding_rands.rand_1.mul(&mu_challenges[num_inputs]);
            let a_randomness = Self::combine_randomness(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.rand_1)),
                combined_challenges,
                Some(&hiding_rand_addend_1),
            );

            let hiding_rand_addend_2 = hiding_rands.rand_2.mul(&mu_challenges[1]);
            let b_randomness = Self::combine_randomness(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.rand_2))
                    .rev(),
                nu_challenges,
                Some(&hiding_rand_addend_2),
            );

            let hiding_rand_addend_3 = hiding_rands.rand_3.mul(&mu_challenges[num_inputs]);
            let product_randomness = Self::combine_randomness(
                input_witnesses
                    .iter()
                    .map(|witness| witness.randomness.as_ref().map(|r| &r.rand_3)),
                &mu_challenges,
                Some(&hiding_rand_addend_3),
            )
            .mul(&nu_challenges[num_inputs - 1]);

            Some(InputWitnessRandomness {
                rand_1: a_randomness,
                rand_2: b_randomness,
                rand_3: product_randomness,
            })
        } else {
            None
        };

        InputWitness {
            a_vec: a_opening_vec,
            b_vec: b_opening_vec,
            randomness,
        }
    }
}

impl<G> AccumulationScheme<ConstraintF<G>> for ASForHadamardProducts<G>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
{
    type PublicParameters = ();
    type PredicateParams = ();
    type PredicateIndex = usize;

    type ProverKey = PedersenCommitmentCK<G>;
    type VerifierKey = usize;
    type DeciderKey = PedersenCommitmentCK<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = InputWitness<G::ScalarField>;
    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = InputWitness<G::ScalarField>;
    type Proof = Proof<G>;
    type Error = BoxedError;

    fn setup(_rng: &mut impl RngCore) -> Result<Self::PublicParameters, Self::Error> {
        Ok(())
    }

    fn index(
        _public_params: &Self::PublicParameters,
        _predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let pedersen_pp = PedersenCommitment::setup(*predicate_index);
        let ck = PedersenCommitment::trim(&pedersen_pp, *predicate_index);

        Ok((ck.clone(), *predicate_index, ck))
    }

    fn prove<'a, S: CryptographicSponge<ConstraintF<G>>>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, ConstraintF<G>, Self>>,
        old_accumulators: impl IntoIterator<Item = AccumulatorRef<'a, ConstraintF<G>, Self>>,
        make_zk: MakeZK<'_>,
        sponge: Option<S>,
    ) -> Result<(Accumulator<ConstraintF<G>, Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let inputs = inputs.into_iter().collect::<Vec<_>>();
        let old_accumulators = old_accumulators.into_iter().collect::<Vec<_>>();

        if inputs.len() + old_accumulators.len() == 0 {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate.".to_string(),
            )));
        }

        let hp_vec_len = if old_accumulators.len() == 0 {
            inputs[0].witness.a_vec.len()
        } else {
            old_accumulators[0].witness.a_vec.len()
        };

        // Combine inputs and accumulators to be processed together
        let mut all_input_instances = inputs
            .iter()
            .chain(&old_accumulators)
            .map(|input| input.instance)
            .collect::<Vec<_>>();

        let mut all_input_witnesses = inputs
            .iter()
            .map(|input| {
                Self::check_input_witness_structure(input.witness, prover_key, hp_vec_len, false)
            })
            .chain(old_accumulators.iter().map(|accumulator| {
                Self::check_input_witness_structure(
                    accumulator.witness,
                    prover_key,
                    hp_vec_len,
                    true,
                )
            }))
            .collect::<Result<Vec<&InputWitness<G::ScalarField>>, BoxedError>>()?;

        let (make_zk_enabled, rng) = make_zk.into_components();
        if !make_zk_enabled {
            for witness in &all_input_witnesses {
                if witness.randomness.is_some() {
                    return Err(BoxedError::new(ASError::MissingRng(
                        "Accumulating inputs with hiding requires rng.".to_string(),
                    )));
                }
            }
        }

        let mut num_inputs = all_input_instances.len();

        let default_input_instance;
        let default_input_witness;

        if make_zk_enabled && num_inputs == 1 {
            default_input_instance = Some(InputInstance::default());
            default_input_witness = Some(InputWitness::default());

            num_inputs += 1;
            all_input_instances.push(default_input_instance.as_ref().unwrap());
            all_input_witnesses.push(default_input_witness.as_ref().unwrap());
        }

        let (hiding_vecs, hiding_rands, hiding_comms) = if make_zk_enabled {
            assert!(rng.is_some());
            let rng = rng.unwrap();

            let a = vec![G::ScalarField::rand(rng); hp_vec_len];
            let b = vec![G::ScalarField::rand(rng); hp_vec_len];

            let rand_1 = G::ScalarField::rand(rng);
            let rand_2 = G::ScalarField::rand(rng);
            let rand_3 = G::ScalarField::rand(rng);

            let comm_1 = PedersenCommitment::commit(prover_key, a.as_slice(), Some(rand_1));
            let comm_2 = PedersenCommitment::commit(prover_key, b.as_slice(), Some(rand_2));

            let comm_3 = {
                let rand_prod_1 =
                    Self::compute_hp(a.as_slice(), all_input_witnesses[0].b_vec.as_slice());

                let rand_prod_2 = Self::compute_hp(
                    all_input_witnesses.last().unwrap().a_vec.as_slice(),
                    b.as_slice(),
                );

                let rand_prods_sum = Self::combine_vectors(
                    vec![&rand_prod_1, &rand_prod_2],
                    &[G::ScalarField::one(), G::ScalarField::one()],
                    None,
                );

                PedersenCommitment::commit(prover_key, rand_prods_sum.as_slice(), Some(rand_3))
            };

            let rands = InputWitnessRandomness {
                rand_1,
                rand_2,
                rand_3,
            };

            let comms = ProofHidingCommitments {
                comm_1,
                comm_2,
                comm_3,
            };

            (Some((a, b)), Some(rands), Some(comms))
        } else {
            (None, None, None)
        };

        let mut challenges_sponge = sponge;
        absorb!(
            &mut challenges_sponge,
            prover_key.supported_num_elems() as u64,
            all_input_instances,
            hiding_comms
        );

        let mu_challenges =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_inputs, make_zk_enabled);

        let t_vecs: Vec<Vec<G::ScalarField>> = Self::compute_t_vecs(
            all_input_witnesses.as_slice(),
            mu_challenges.as_slice(),
            hp_vec_len,
            hiding_vecs.as_ref(),
        );

        let t_comms = Self::compute_t_comms(prover_key, &t_vecs)?;
        let proof = Proof {
            t_comms,
            hiding_comms,
        };

        challenges_sponge.absorb(&proof.t_comms);

        let nu_challenges = Self::squeeze_nu_challenges(&mut challenges_sponge, num_inputs);

        let mut combined_challenges = Vec::with_capacity(num_inputs);
        for (mu, nu) in mu_challenges.iter().zip(&nu_challenges) {
            combined_challenges.push(mu.clone().mul(nu));
        }

        let accumulator_instance = Self::compute_combined_hp_commitments(
            all_input_instances.as_slice(),
            &proof,
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
        );

        let accumulator_witness = Self::compute_combined_hp_openings(
            all_input_witnesses.as_slice(),
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
            hiding_vecs.as_ref(),
            hiding_rands.as_ref(),
        );

        let accumulator = Accumulator::<_, Self> {
            instance: accumulator_instance,
            witness: accumulator_witness,
        };

        Ok((accumulator, proof))
    }

    fn verify<'a, S: CryptographicSponge<ConstraintF<G>>>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let sponge = sponge.unwrap_or_else(|| S::new());

        let mut all_input_instances = input_instances
            .into_iter()
            .chain(old_accumulator_instances)
            .collect::<Vec<_>>();

        if all_input_instances.len() == 0 {
            return Ok(false);
        }

        if !Self::check_proof_structure(proof, all_input_instances.len()) {
            return Ok(false);
        }

        let mut num_inputs = all_input_instances.len();
        let make_zk = proof.hiding_comms.is_some();

        let default_input_instance;
        if make_zk && num_inputs == 1 {
            default_input_instance = Some(InputInstance::default());

            num_inputs += 1;
            all_input_instances.push(default_input_instance.as_ref().unwrap());
        }

        let mut challenges_sponge = sponge;
        absorb!(
            &mut challenges_sponge,
            *verifier_key as u64,
            all_input_instances,
            proof.hiding_comms
        );

        let mu_challenges =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_inputs, make_zk);

        challenges_sponge.absorb(&proof.t_comms);

        let nu_challenges = Self::squeeze_nu_challenges(&mut challenges_sponge, num_inputs);

        let mut combined_challenges = Vec::with_capacity(num_inputs);
        for (mu, nu) in mu_challenges.iter().zip(&nu_challenges) {
            combined_challenges.push(mu.clone().mul(nu));
        }

        let accumulator_instance = Self::compute_combined_hp_commitments(
            all_input_instances.as_slice(),
            proof,
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
        );

        Ok(accumulator_instance.eq(new_accumulator_instance))
    }

    fn decide<'a, S: CryptographicSponge<ConstraintF<G>>>(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, ConstraintF<G>, Self>,
        _sponge: Option<S>,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        let instance = accumulator.instance;
        let witness = accumulator.witness;
        let randomness = witness.randomness.as_ref();

        let a_vec = &witness.a_vec;
        let b_vec = &witness.b_vec;
        let product = Self::compute_hp(a_vec.as_slice(), b_vec.as_slice());

        let test_comm_1 =
            PedersenCommitment::commit(decider_key, a_vec.as_slice(), randomness.map(|r| r.rand_1));
        let test_comm_2 =
            PedersenCommitment::commit(decider_key, b_vec.as_slice(), randomness.map(|r| r.rand_2));
        let test_comm_3 = PedersenCommitment::commit(
            decider_key,
            product.as_slice(),
            randomness.map(|r| r.rand_3),
        );

        let result = test_comm_1.eq(&instance.comm_1)
            && test_comm_2.eq(&instance.comm_2)
            && test_comm_3.eq(&instance.comm_3);

        Ok(result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::hp_as::data_structures::{InputInstance, InputWitness, InputWitnessRandomness};
    use crate::hp_as::ASForHadamardProducts;
    use crate::tests::*;
    use crate::AccumulationScheme;
    use crate::ConstraintF;
    use ark_ec::AffineCurve;
    use ark_poly_commit::trivial_pc::{CommitterKey as PedersenCommitmentCK, PedersenCommitment};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::Absorbable;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct ASForHPTestParams {
        pub(crate) vector_len: usize,
        pub(crate) make_zk: bool,
    }

    impl TestParameters for ASForHPTestParams {
        fn make_zk(&self) -> bool {
            self.make_zk
        }
    }

    pub struct ASForHPTestInput {}

    impl<G> ASTestInput<ConstraintF<G>, ASForHadamardProducts<G>> for ASForHPTestInput
    where
        G: AffineCurve + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
    {
        type TestParams = ASForHPTestParams;
        type InputParams = (PedersenCommitmentCK<G>, bool);

        fn setup(
            test_params: &Self::TestParams,
            _rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <ASForHadamardProducts<G> as AccumulationScheme<ConstraintF<G>>>::PredicateParams,
            <ASForHadamardProducts<G> as AccumulationScheme<ConstraintF<G>>>::PredicateIndex,
        ) {
            let pp = PedersenCommitment::setup(test_params.vector_len);
            let ck = PedersenCommitment::trim(&pp, test_params.vector_len);
            ((ck, test_params.make_zk), (), test_params.vector_len)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            _rng: &mut impl RngCore,
        ) -> Vec<Input<ConstraintF<G>, ASForHadamardProducts<G>>> {
            let mut rng = test_rng();
            let vector_len = input_params.0.supported_num_elems();

            (0..num_inputs)
                .map(|_| {
                    let a_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let b_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let product =
                        ASForHadamardProducts::<G>::compute_hp(a_vec.as_slice(), b_vec.as_slice());

                    let randomness = if input_params.1 {
                        let rand_1 = G::ScalarField::rand(&mut rng);
                        let rand_2 = G::ScalarField::rand(&mut rng);
                        let rand_3 = G::ScalarField::rand(&mut rng);
                        Some(InputWitnessRandomness {
                            rand_1,
                            rand_2,
                            rand_3,
                        })
                    } else {
                        None
                    };

                    let comm_1 = PedersenCommitment::commit(
                        &input_params.0,
                        a_vec.as_slice(),
                        randomness.as_ref().map(|r| r.rand_1),
                    );

                    let comm_2 = PedersenCommitment::commit(
                        &input_params.0,
                        b_vec.as_slice(),
                        randomness.as_ref().map(|r| r.rand_2),
                    );

                    let comm_3 = PedersenCommitment::commit(
                        &input_params.0,
                        product.as_slice(),
                        randomness.as_ref().map(|r| r.rand_3),
                    );

                    let instance = InputInstance {
                        comm_1,
                        comm_2,
                        comm_3,
                    };

                    let witness = InputWitness {
                        a_vec,
                        b_vec,
                        randomness,
                    };

                    Input::<_, ASForHadamardProducts<G>> { instance, witness }
                })
                .collect::<Vec<_>>()
        }
    }

    type G = ark_pallas::Affine;
    type CF = ark_pallas::Fq;

    type Sponge = PoseidonSponge<CF>;

    type AS = ASForHadamardProducts<G>;
    type I = ASForHPTestInput;

    type Tests = ASTests<CF, AS, I, Sponge>;

    #[test]
    pub fn single_input_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::single_input_initialization_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_initialization_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_initialization_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_inputs_initialization_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        Tests::simple_accumulation_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_no_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_zk() -> Result<(), BoxedError> {
        Tests::multiple_accumulations_multiple_inputs_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        Tests::accumulators_only_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_no_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: false,
        })
    }

    #[test]
    pub fn no_accumulators_or_inputs_fail_test_zk() -> Result<(), BoxedError> {
        Tests::no_accumulators_or_inputs_fail_test(&ASForHPTestParams {
            vector_len: 11,
            make_zk: true,
        })
    }
}
