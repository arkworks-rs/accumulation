use crate::constraints::ConstraintF;
use crate::data_structures::{Accumulator, AccumulatorRef, InputRef};
use crate::error::{ASError, BoxedError};
use crate::{AccumulationScheme, MakeZK};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{One, ToConstraintField, Zero};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::pedersen::{CommitterKey as PedersenCommitmentCK, PedersenCommitment};
use ark_poly_commit::UVPolynomial;
use ark_sponge::{absorb, Absorbable, CryptographicSponge, FieldElementSize};
use ark_std::UniformRand;
use data_structures::*;
use rand_core::RngCore;
use std::marker::PhantomData;
use std::ops::Mul;

pub mod data_structures;

pub mod constraints;

pub struct HadamardProductAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    _affine: PhantomData<G>,
    _sponge: PhantomData<S>,
}

impl<G, S> HadamardProductAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    fn squeeze_mu_challenges(
        sponge: &mut S,
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

    fn squeeze_nu_challenges(sponge: &mut S, num_inputs: usize) -> Vec<G::ScalarField> {
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

            // TODO: Change to nlogn mul
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

            let comm = PedersenCommitment::commit(ck, t_vec.as_slice(), None)
                .map_err(BoxedError::new)?
                .0;

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
        // TODO: Replace into with batch normalization to affine

        let num_inputs = input_instances.len();

        let hiding_comm_addend_1 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| hiding_comms.comm_1.mul(mu_challenges[num_inputs].into()));

        let combined_comm_1: G = Self::combine_commitments(
            input_instances.iter().map(|instance| &instance.comm_1),
            combined_challenges,
            hiding_comm_addend_1.as_ref(),
        )
        .into();

        let hiding_comm_addend_2 = proof
            .hiding_comms
            .as_ref()
            .map(|hiding_comms| hiding_comms.comm_2.mul(mu_challenges[1].into()));

        let combined_comm_2: G = Self::combine_commitments(
            input_instances
                .iter()
                .map(|instance| &instance.comm_2)
                .rev(),
            nu_challenges,
            hiding_comm_addend_2.as_ref(),
        )
        .into();

        let combined_comm_3: G = {
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

            (t_comm_low_addend + &t_comm_high_addend + &comm_3_addend).into()
        };

        InputInstance {
            comm_1: combined_comm_1,
            comm_2: combined_comm_2,
            comm_3: combined_comm_3,
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

impl<G, S> AccumulationScheme for HadamardProductAS<G, S>
where
    G: AffineCurve + Absorbable<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
{
    type UniversalParams = ();
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

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        _predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let pedersen_pp = PedersenCommitment::setup(*predicate_index).map_err(BoxedError::new)?;
        let ck =
            PedersenCommitment::trim(&pedersen_pp, *predicate_index).map_err(BoxedError::new)?;
        Ok((ck.clone(), *predicate_index, ck))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = InputRef<'a, Self>>,
        accumulators: impl IntoIterator<Item = AccumulatorRef<'a, Self>>,
        make_zk: MakeZK,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let inputs = inputs.into_iter().collect::<Vec<_>>();
        let accumulators = accumulators.into_iter().collect::<Vec<_>>();

        // Combine inputs and accumulators to be processed together
        let mut input_instances = inputs
            .iter()
            .chain(&accumulators)
            .map(|input| input.instance)
            .collect::<Vec<_>>();

        if input_instances.len() == 0 {
            return Err(BoxedError::new(ASError::MissingAccumulatorsAndInputs(
                "No inputs or accumulators to accumulate".to_string(),
            )));
        }

        let mut input_witnesses = inputs
            .iter()
            .chain(&accumulators)
            .map(|input| input.witness)
            .collect::<Vec<_>>();

        let (make_zk, rng) = make_zk.into_components(|| {
            input_witnesses.iter().fold(false, |make_zk, witness| {
                make_zk || witness.randomness.is_some()
            })
        });

        if make_zk && rng.is_none() {
            return Err(BoxedError::new(ASError::MissingRng(
                "Accumulating inputs with hiding requires rng.".to_string(),
            )));
        }

        let mut num_inputs = input_instances.len();
        let hp_vec_len = prover_key.supported_elems_len();

        let default_input_instance;
        let default_input_witness;

        if make_zk && num_inputs == 1 {
            default_input_instance = Some(InputInstance::default());
            default_input_witness = Some(InputWitness::default());

            num_inputs += 1;
            input_instances.push(default_input_instance.as_ref().unwrap());
            input_witnesses.push(default_input_witness.as_ref().unwrap());
        }

        let (hiding_vecs, hiding_rands, hiding_comms) = if make_zk {
            assert!(rng.is_some());
            let rng = rng.unwrap();

            let a = vec![G::ScalarField::rand(rng); hp_vec_len];
            let b = vec![G::ScalarField::rand(rng); hp_vec_len];

            let rand_1 = G::ScalarField::rand(rng);
            let rand_2 = G::ScalarField::rand(rng);
            let rand_3 = G::ScalarField::rand(rng);

            let comm_1 = PedersenCommitment::commit(prover_key, a.as_slice(), Some(rand_1))
                .map_err(BoxedError::new)?
                .0;

            let comm_2 = PedersenCommitment::commit(prover_key, b.as_slice(), Some(rand_2))
                .map_err(BoxedError::new)?
                .0;

            let comm_3 = {
                let rand_prod_1 =
                    Self::compute_hp(a.as_slice(), input_witnesses[0].b_vec.as_slice());

                let rand_prod_2 = Self::compute_hp(
                    input_witnesses.last().unwrap().a_vec.as_slice(),
                    b.as_slice(),
                );

                let rand_prods_sum = Self::combine_vectors(
                    vec![&rand_prod_1, &rand_prod_2],
                    &[G::ScalarField::one(), G::ScalarField::one()],
                    None,
                );

                PedersenCommitment::commit(prover_key, rand_prods_sum.as_slice(), Some(rand_3))
                    .map_err(BoxedError::new)?
                    .0
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

        let mut challenges_sponge = S::new();
        absorb!(
            &mut challenges_sponge,
            prover_key.supported_elems_len() as u64,
            input_instances,
            hiding_comms
        );

        let mu_challenges =
            Self::squeeze_mu_challenges(&mut challenges_sponge, num_inputs, make_zk);

        let t_vecs: Vec<Vec<G::ScalarField>> = Self::compute_t_vecs(
            input_witnesses.as_slice(),
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
            input_instances.as_slice(),
            &proof,
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
        );

        let accumulator_witness = Self::compute_combined_hp_openings(
            input_witnesses.as_slice(),
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
            hiding_vecs.as_ref(),
            hiding_rands.as_ref(),
        );

        let accumulator = Accumulator::<Self> {
            instance: accumulator_instance,
            witness: accumulator_witness,
        };

        Ok((accumulator, proof))
    }

    fn verify<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        // TODO: Validate input instances
        let mut input_instances = input_instances
            .into_iter()
            .chain(accumulator_instances)
            .collect::<Vec<_>>();

        if input_instances.len() == 0 {
            return Ok(false);
        }

        let mut num_inputs = input_instances.len();
        let make_zk = proof.hiding_comms.is_some();

        let default_input_instance;
        if make_zk && num_inputs == 1 {
            default_input_instance = Some(InputInstance::default());

            num_inputs += 1;
            input_instances.push(default_input_instance.as_ref().unwrap());
        }

        let mut challenges_sponge = S::new();
        absorb!(
            &mut challenges_sponge,
            *verifier_key as u64,
            input_instances,
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
            input_instances.as_slice(),
            proof,
            mu_challenges.as_slice(),
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
        );

        Ok(accumulator_instance.eq(new_accumulator_instance))
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: AccumulatorRef<'_, Self>,
    ) -> Result<bool, Self::Error> {
        let instance = accumulator.instance;
        let witness = accumulator.witness;
        let randomness = witness.randomness.as_ref();

        let a_vec = &witness.a_vec;
        let b_vec = &witness.b_vec;
        let product = Self::compute_hp(a_vec.as_slice(), b_vec.as_slice());

        let test_comm_1 =
            PedersenCommitment::commit(decider_key, a_vec.as_slice(), randomness.map(|r| r.rand_1))
                .map_err(BoxedError::new)?;
        let test_comm_2 =
            PedersenCommitment::commit(decider_key, b_vec.as_slice(), randomness.map(|r| r.rand_2))
                .map_err(BoxedError::new)?;
        let test_comm_3 = PedersenCommitment::commit(
            decider_key,
            product.as_slice(),
            randomness.map(|r| r.rand_3),
        )
        .map_err(BoxedError::new)?;

        let result = test_comm_1.0.eq(&instance.comm_1)
            && test_comm_2.0.eq(&instance.comm_2)
            && test_comm_3.0.eq(&instance.comm_3);

        Ok(result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ConstraintF;
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::hp_as::data_structures::{InputInstance, InputWitness, InputWitnessRandomness};
    use crate::hp_as::HadamardProductAS;
    use crate::tests::*;
    use crate::AccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ff::ToConstraintField;
    use ark_pallas::{Affine, Fq};
    use ark_poly_commit::pedersen::{CommitterKey as PedersenCommitmentCK, PedersenCommitment};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::{Absorbable, CryptographicSponge};
    use ark_std::test_rng;
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct HpASTestParams {
        pub(crate) vector_len: usize,
        pub(crate) make_zk: bool,
    }

    pub struct HpASTestInput {}

    impl<G, S> ASTestInput<HadamardProductAS<G, S>> for HpASTestInput
    where
        G: AffineCurve + Absorbable<ConstraintF<G>>,
        ConstraintF<G>: Absorbable<ConstraintF<G>>,
        S: CryptographicSponge<ConstraintF<G>>,
    {
        type TestParams = HpASTestParams;
        type InputParams = (PedersenCommitmentCK<G>, bool);

        fn setup(
            test_params: &Self::TestParams,
            _rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <HadamardProductAS<G, S> as AccumulationScheme>::PredicateParams,
            <HadamardProductAS<G, S> as AccumulationScheme>::PredicateIndex,
        ) {
            let pp = PedersenCommitment::setup(test_params.vector_len).unwrap();
            let ck = PedersenCommitment::trim(&pp, test_params.vector_len).unwrap();
            ((ck, test_params.make_zk), (), test_params.vector_len)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            _rng: &mut impl RngCore,
        ) -> Vec<Input<HadamardProductAS<G, S>>> {
            let mut rng = test_rng();
            let vector_len = input_params.0.supported_elems_len();

            (0..num_inputs)
                .map(|_| {
                    let a_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let b_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let product =
                        HadamardProductAS::<G, S>::compute_hp(a_vec.as_slice(), b_vec.as_slice());

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
                    )
                    .unwrap()
                    .0;
                    let comm_2 = PedersenCommitment::commit(
                        &input_params.0,
                        b_vec.as_slice(),
                        randomness.as_ref().map(|r| r.rand_2),
                    )
                    .unwrap()
                    .0;
                    let comm_3 = PedersenCommitment::commit(
                        &input_params.0,
                        product.as_slice(),
                        randomness.as_ref().map(|r| r.rand_3),
                    )
                    .unwrap()
                    .0;

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
                    Input::<HadamardProductAS<G, S>> { instance, witness }
                })
                .collect::<Vec<_>>()
        }
    }

    type AS = HadamardProductAS<Affine, PoseidonSponge<Fq>>;
    type I = HpASTestInput;

    #[test]
    pub fn single_input_initialization_test_no_zk() -> Result<(), BoxedError> {
        crate::tests::single_input_initialization_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn single_input_initialization_test_zk() -> Result<(), BoxedError> {
        crate::tests::single_input_initialization_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_inputs_initialization_test_no_zk() -> Result<(), BoxedError> {
        crate::tests::multiple_inputs_initialization_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_input_initialization_test_zk() -> Result<(), BoxedError> {
        crate::tests::multiple_inputs_initialization_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn simple_accumulation_test_no_zk() -> Result<(), BoxedError> {
        crate::tests::simple_accumulation_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn simple_accumulation_test_zk() -> Result<(), BoxedError> {
        crate::tests::simple_accumulation_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_no_zk() -> Result<(), BoxedError> {
        crate::tests::multiple_accumulations_multiple_inputs_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn multiple_accumulations_multiple_inputs_test_zk() -> Result<(), BoxedError> {
        crate::tests::multiple_accumulations_multiple_inputs_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: true,
        })
    }

    #[test]
    pub fn accumulators_only_test_no_zk() -> Result<(), BoxedError> {
        crate::tests::accumulators_only_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: false,
        })
    }

    #[test]
    pub fn accumulators_only_test_zk() -> Result<(), BoxedError> {
        crate::tests::accumulators_only_test::<AS, I>(&HpASTestParams {
            vector_len: 8,
            make_zk: true,
        })
    }
}
