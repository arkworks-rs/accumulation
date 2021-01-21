use crate::data_structures::{Accumulator, Input};
use crate::error::BoxedError;
use crate::hp_as::data_structures::{InputInstance, InputWitness, Proof};
use crate::AidedAccumulationScheme;
use ark_ec::group::Group;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::to_bytes;
use ark_ff::Field;
use ark_ff::One;
use ark_ff::Zero;
use ark_ff::{PrimeField, ToConstraintField};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::pedersen::{
    CommitterKey as PedersenCommitmentCK, PedersenCommitment,
    UniversalParams as PedersenCommitmentPP,
};
use ark_poly_commit::UVPolynomial;
use ark_sponge::CryptographicSponge;
use ark_std::UniformRand;
use rand_core::RngCore;
use std::marker::PhantomData;
use std::ops::Mul;

pub mod data_structures;

pub struct HPAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
    S: CryptographicSponge<CF>,
{
    _affine: PhantomData<G>,
    _constraint_field: PhantomData<CF>,
    _sponge: PhantomData<S>,
}

impl<G, CF, S> HPAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
    S: CryptographicSponge<CF>,
{
    // Assumes the length of a_vec and b_vec is hp_vec_len or below.
    fn compute_t_vecs(
        input_witnesses: &[&InputWitness<G>],
        mu_challenges: &[G::ScalarField],
        hp_vec_len: usize,
    ) -> Vec<Vec<G::ScalarField>> {
        let num_inputs = input_witnesses.len();
        assert!(num_inputs <= mu_challenges.len());

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

            let a_poly = DensePolynomial::from_coefficients_vec(a_coeffs);
            let b_poly = DensePolynomial::from_coefficients_vec(b_coeffs);

            // TODO: Change to nlogn mul
            let product_polynomial = a_poly.naive_mul(&b_poly);
            let mut product_polynomial_coeffs = product_polynomial.coeffs;

            assert!(product_polynomial_coeffs.len() <= 2 * num_inputs - 1);
            product_polynomial_coeffs.resize_with(2 * num_inputs - 1, || G::ScalarField::zero());

            for i in 0..(2 * num_inputs - 1) {
                t_vecs[i].push(product_polynomial_coeffs[i].clone());
            }
        }

        t_vecs
    }

    /// Outputs commitments to each t_vec, excluding the `n-1`th t_vec
    /// The commitments are split into two, one computed on everything
    /// before the `n-1`th t_vec and one computed on everything after the `n-1`th t_vec.
    fn compute_t_comms(
        ck: &PedersenCommitmentCK<G>,
        t_vecs: &Vec<Vec<G::ScalarField>>,
    ) -> Result<(Vec<G>, Vec<G>), BoxedError> {
        if t_vecs.len() == 0 {
            return Ok((Vec::new(), Vec::new()));
        }

        let num_inputs = (t_vecs.len() + 1) / 2;

        let mut t_comms = (
            Vec::with_capacity(num_inputs - 1),
            Vec::with_capacity(num_inputs - 1),
        );

        for (i, t_vec) in t_vecs.iter().enumerate() {
            if i == num_inputs - 1 {
                continue;
            }

            let comm = PedersenCommitment::commit(ck, t_vec.as_slice(), None)
                .map_err(BoxedError::new)?
                .0;

            (if i < num_inputs - 1 {
                &mut t_comms.0
            } else {
                &mut t_comms.1
            })
            .push(comm)
        }

        Ok(t_comms)
    }

    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = &'a G>,
        challenges: &[G::ScalarField],
    ) -> G::Projective {
        let mut combined_commitment = G::Projective::zero();
        for (i, commitment) in commitments.into_iter().enumerate() {
            combined_commitment += &commitment.mul(challenges[i].clone());
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

        let combined_comm_1: G = Self::combine_commitments(
            input_instances.iter().map(|instance| &instance.comm_1),
            combined_challenges,
        )
        .into();

        let combined_comm_2: G = Self::combine_commitments(
            input_instances
                .iter()
                .map(|instance| &instance.comm_2)
                .rev(),
            nu_challenges,
        )
        .into();

        let combined_comm_3: G = {
            let t_comm_low_addend =
                Self::combine_commitments(proof.t_comms.0.iter(), &nu_challenges);
            let t_comm_high_addend =
                Self::combine_commitments(proof.t_comms.1.iter(), &nu_challenges[num_inputs..]);

            let comm_3_addend = Self::combine_commitments(
                input_instances.iter().map(|instance| &instance.comm_3),
                &mu_challenges,
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

    fn sum_vectors<'a>(
        vectors: impl IntoIterator<Item = &'a Vec<G::ScalarField>>,
        challenges: &[G::ScalarField],
    ) -> Vec<G::ScalarField> {
        let mut output = Vec::new();
        for (ni, vector) in vectors.into_iter().enumerate() {
            for (li, elem) in vector.into_iter().enumerate() {
                let product = challenges[ni].clone() * elem;
                if li >= output.len() {
                    output.push(product);
                } else {
                    output[li] += product;
                }
            }
        }

        output
    }

    fn compute_combined_hp_openings(
        input_witnesses: &[&InputWitness<G>],
        nu_challenges: &[G::ScalarField],
        combined_challenges: &[G::ScalarField],
    ) -> InputWitness<G> {
        let a_opening_vec = Self::sum_vectors(
            input_witnesses.iter().map(|witness| &witness.a_vec),
            combined_challenges,
        );

        let b_opening_vec = Self::sum_vectors(
            input_witnesses.iter().map(|witness| &witness.b_vec).rev(),
            nu_challenges,
        );

        InputWitness {
            a_vec: a_opening_vec,
            b_vec: b_opening_vec,
        }
    }

    fn compute_hp(a_vec: &[G::ScalarField], b_vec: &[G::ScalarField]) -> Vec<G::ScalarField> {
        let mut product = Vec::with_capacity(a_vec.len().min(b_vec.len()));
        for (a, b) in a_vec.iter().zip(b_vec.iter()) {
            product.push(a.clone() * b);
        }

        product
    }
}

impl<G, CF, S> AidedAccumulationScheme for HPAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
    S: CryptographicSponge<CF>,
{
    type UniversalParams = ();
    type PredicateParams = PedersenCommitmentPP<G>;
    type PredicateIndex = usize;

    type ProverKey = PedersenCommitmentCK<G>;
    type VerifierKey = ();
    type DeciderKey = PedersenCommitmentCK<G>;

    type InputInstance = InputInstance<G>;
    type InputWitness = InputWitness<G>;
    type AccumulatorInstance = InputInstance<G>;
    type AccumulatorWitness = InputWitness<G>;
    type Proof = Proof<G>;
    type Error = BoxedError;

    fn generate(_rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        Ok(())
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let ck = PedersenCommitment::trim(&predicate_params, *predicate_index)
            .map_err(BoxedError::new)?;
        Ok((ck.clone(), (), ck))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = &'a Input<Self>>,
        accumulators: impl IntoIterator<Item = &'a Accumulator<Self>>,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        // TODO: What if there are no inputs
        let inputs: Vec<&Input<Self>> = inputs.into_iter().collect();
        let accumulators: Vec<&Accumulator<Self>> = accumulators.into_iter().collect();

        // Combine inputs and accumulators to be processed together
        let input_instances = inputs
            .iter()
            .map(|input| &input.instance)
            .chain(accumulators.iter().map(|accumulator| &accumulator.instance))
            .collect::<Vec<_>>();

        let input_witnesses = inputs
            .iter()
            .map(|input| &input.witness)
            .chain(accumulators.iter().map(|accumulator| &accumulator.witness))
            .collect::<Vec<_>>();

        let mut challenges_sponge = S::new();
        // TODO: Absorb vk
        for input_instance in input_instances.iter() {
            challenges_sponge.absorb(input_instance);
        }

        let num_inputs = input_instances.len();
        let hp_vec_len = prover_key.supported_elems_len();

        // TODO: Squeeze shorter bits
        let mu_challenges: Vec<G::ScalarField> =
            challenges_sponge.squeeze_nonnative_field_elements(num_inputs);

        // Matrix of dimension hp_vec_len x num_inputs
        let t_vecs: Vec<Vec<G::ScalarField>> = Self::compute_t_vecs(
            input_witnesses.as_slice(),
            mu_challenges.as_slice(),
            hp_vec_len,
        );

        let t_comms = Self::compute_t_comms(prover_key, &t_vecs)?;
        let proof = Proof { t_comms };

        challenges_sponge.absorb(&proof);

        let nu_challenge: G::ScalarField = challenges_sponge
            .squeeze_nonnative_field_elements(1)
            .pop()
            .unwrap();
        let mut nu_challenges = Vec::with_capacity(2 * num_inputs - 1);

        let mut cur_nu_challenge = G::ScalarField::one();
        for _ in 0..(2 * num_inputs - 1) {
            nu_challenges.push(cur_nu_challenge);
            cur_nu_challenge *= &nu_challenge;
        }

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
            nu_challenges.as_slice(),
            combined_challenges.as_slice(),
        );

        let accumulator = Accumulator {
            instance: accumulator_instance,
            witness: accumulator_witness,
        };

        Ok((accumulator, proof))
    }

    fn verify<'a>(
        _verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>
    where
        Self: 'a,
    {
        // TODO: Validate input instances
        let input_instances = input_instances
            .into_iter()
            .chain(accumulator_instances)
            .collect::<Vec<_>>();
        let num_inputs = input_instances.len();

        let mut challenges_sponge = S::new();
        // TODO: Absorb vk
        for input_instance in input_instances.iter() {
            challenges_sponge.absorb(input_instance);
        }

        // TODO: Squeeze shorter bits
        let mu_challenges: Vec<G::ScalarField> =
            challenges_sponge.squeeze_nonnative_field_elements(num_inputs);

        challenges_sponge.absorb(proof);

        let nu_challenge: G::ScalarField = challenges_sponge
            .squeeze_nonnative_field_elements(1)
            .pop()
            .unwrap();
        let mut nu_challenges = Vec::with_capacity(2 * num_inputs - 1);

        let mut cur_nu_challenge = G::ScalarField::one();
        for _ in 0..(2 * num_inputs - 1) {
            nu_challenges.push(cur_nu_challenge);
            cur_nu_challenge *= &nu_challenge;
        }

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
        accumulator: &Accumulator<Self>,
    ) -> Result<bool, Self::Error> {
        let instance = &accumulator.instance;
        let witness = &accumulator.witness;

        let a_vec = &witness.a_vec;
        let b_vec = &witness.b_vec;
        let mut product = Self::compute_hp(a_vec.as_slice(), b_vec.as_slice());

        let test_comm_1 = PedersenCommitment::commit(decider_key, a_vec.as_slice(), None)
            .map_err(BoxedError::new)?;
        let test_comm_2 = PedersenCommitment::commit(decider_key, b_vec.as_slice(), None)
            .map_err(BoxedError::new)?;
        let test_comm_3 = PedersenCommitment::commit(decider_key, product.as_slice(), None)
            .map_err(BoxedError::new)?;

        assert!(test_comm_1.0.eq(&instance.comm_1));
        assert!(test_comm_2.0.eq(&instance.comm_2));
        let result = test_comm_3.0.eq(&instance.comm_3);

        Ok(result)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::data_structures::Input;
    use crate::error::BoxedError;
    use crate::hp_as::data_structures::{InputInstance, InputWitness};
    use crate::hp_as::HPAidedAccumulationScheme;
    use crate::tests::*;
    use crate::AidedAccumulationScheme;
    use ark_ec::AffineCurve;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq};
    use ark_ff::One;
    use ark_ff::{PrimeField, ToConstraintField};
    use ark_poly_commit::pedersen::{CommitterKey as PedersenCommitmentCK, PedersenCommitment};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::CryptographicSponge;
    use ark_std::test_rng;
    use ark_std::UniformRand;
    use rand_core::RngCore;

    pub struct HPAidedAccumulationSchemeTestInput {}

    impl<G, CF, S> AccumulationSchemeTestInput<HPAidedAccumulationScheme<G, CF, S>>
        for HPAidedAccumulationSchemeTestInput
    where
        G: AffineCurve + ToConstraintField<CF>,
        CF: PrimeField,
        S: CryptographicSponge<CF>,
    {
        type TestParams = usize;
        type InputParams = PedersenCommitmentCK<G>;

        fn setup(
            test_params: &Self::TestParams,
            rng: &mut impl RngCore,
        ) -> (
            Self::InputParams,
            <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::PredicateParams,
            <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::PredicateIndex,
        ) {
            let mut rng = test_rng();
            let pp = PedersenCommitment::setup(*test_params, &mut rng).unwrap();
            let ck = PedersenCommitment::trim(&pp, *test_params).unwrap();
            (ck, pp, *test_params)
        }

        fn generate_inputs(
            input_params: &Self::InputParams,
            num_inputs: usize,
            rng: &mut impl RngCore,
        ) -> Vec<Input<HPAidedAccumulationScheme<G, CF, S>>> {
            let mut rng = test_rng();
            let vector_len = input_params.supported_elems_len();

            (0..num_inputs)
                .map(|_| {
                    let a_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let b_vec = vec![G::ScalarField::rand(&mut rng); vector_len];
                    let product = HPAidedAccumulationScheme::<G, CF, S>::compute_hp(
                        a_vec.as_slice(),
                        b_vec.as_slice(),
                    );

                    let comm_1 = PedersenCommitment::commit(input_params, a_vec.as_slice(), None)
                        .unwrap()
                        .0;
                    let comm_2 = PedersenCommitment::commit(input_params, b_vec.as_slice(), None)
                        .unwrap()
                        .0;
                    let comm_3 = PedersenCommitment::commit(input_params, product.as_slice(), None)
                        .unwrap()
                        .0;

                    let instance = InputInstance {
                        comm_1,
                        comm_2,
                        comm_3,
                    };

                    let witness = InputWitness { a_vec, b_vec };
                    Input { instance, witness }
                })
                .collect::<Vec<_>>()
        }
    }

    type AS = HPAidedAccumulationScheme<EdwardsAffine, Fq, PoseidonSponge<Fq>>;

    type I = HPAidedAccumulationSchemeTestInput;

    /*
    #[test]
    pub fn hp_single_input_test() -> Result<(), BoxedError> {
        single_input_test::<AS, I>(&8)
    }

     */

    #[test]
    pub fn hp_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_inputs_test::<AS, I>(&8)
    }

    /*
    #[test]
    pub fn hp_multiple_accumulations_test() -> Result<(), BoxedError> {
        multiple_accumulations_test::<AS, I>(&8)
    }

    #[test]
    pub fn hp_multiple_accumulations_multiple_inputs_test() -> Result<(), BoxedError> {
        multiple_accumulations_multiple_inputs_test::<AS, I>(&8)
    }

    #[test]
    pub fn hp_accumulators_only_test() -> Result<(), BoxedError> {
        accumulators_only_test::<AS, I>(&8)
    }
     */
}
