use crate::data_structures::{Accumulator, Input};
use crate::error::BoxedError;
use crate::hp_as::data_structures::{
    InputInstance as HPInputInstance, InputWitness as HPInputWitness,
};
use crate::hp_as::HPAidedAccumulationScheme;
use crate::r1cs_nark::data_structures::{FirstRoundMessage, SecondRoundMessage};
use crate::r1cs_nark::{hash_matrices, matrix_vec_mul, PROTOCOL_NAME as NARK_PROTOCOL_NAME};
use crate::r1cs_nark_as::data_structures::{AccumulatorInstance, AccumulatorWitness, DeciderKey, PredicateIndex, ProverKey, VerifierKey, InputInstance, InputWitness};
use crate::AidedAccumulationScheme;
use ark_ec::AffineCurve;
use ark_ff::{PrimeField, ToConstraintField};
use ark_poly_commit::pedersen::PedersenCommitment;
use ark_sponge::CryptographicSponge;
use rand_core::RngCore;

pub mod data_structures;

pub(crate) const PROTOCOL_NAME: &[u8] = b"Simple-R1CS-NARK-Accumulation-Scheme-2020";

pub struct SimpleNARKAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
    S: CryptographicSponge<CF>, {}

impl<G, CF, S> AidedAccumulationScheme for SimpleNARKAidedAccumulationScheme<G, CF, S>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
    S: CryptographicSponge<CF>,
{
    type UniversalParams =
        <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::UniversalParams;

    type PredicateParams = ();
    type PredicateIndex = PredicateIndex<G::ScalarField>;

    type ProverKey = ProverKey<G>;
    type VerifierKey = VerifierKey;
    type DeciderKey = DeciderKey<G>;
    type InputInstance = InputInstance<G>;
    type InputWitness = InputWitness<G::ScalarField>;
    type AccumulatorInstance = AccumulatorInstance<G>;
    type AccumulatorWitness = AccumulatorWitness<G::ScalarField>;
    type Proof = ();
    type Error = BoxedError;

    fn generate(rng: &mut impl RngCore) -> Result<Self::UniversalParams, Self::Error> {
        <HPAidedAccumulationScheme<G, CF, S> as AidedAccumulationScheme>::generate(rng)
    }

    fn index(
        _universal_params: &Self::UniversalParams,
        _predicate_params: &Self::PredicateParams,
        predicate_index: &Self::PredicateIndex,
    ) -> Result<(Self::ProverKey, Self::VerifierKey, Self::DeciderKey), Self::Error> {
        let a = predicate_index.a.clone();
        let b = predicate_index.b.clone();
        let c = predicate_index.c.clone();

        let nark_matrices_hash = hash_matrices(NARK_PROTOCOL_NAME, &a, &b, &c);
        let as_matrices_hash = hash_matrices(PROTOCOL_NAME, &a, &b, &c);
        let index = predicate_index.index;

        let ped_pp = PedersenCommitment::setup(index).map_err(BoxedError::new)?;
        let ck = PedersenCommitment::trim(&ped_pp, index).map_err(BoxedError::new)?;

        let pk = ProverKey {
            a: a.clone(),
            b: b.clone(),
            c: c.clone(),
            as_matrices_hash,
            nark_matrices_hash,
            index,
            ck: ck.clone(),
        };

        let vk = VerifierKey {
            as_matrices_hash,
            nark_matrices_hash,
            index,
        };

        let dk = DeciderKey { a, b, c, index, ck };

        Ok((pk, vk, dk))
    }

    fn prove<'a>(
        prover_key: &Self::ProverKey,
        inputs: impl IntoIterator<Item = &'a Input<Self>>,
        accumulators: impl IntoIterator<Item = &'a Accumulator<Self>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Accumulator<Self>, Self::Proof), Self::Error>
    where
        Self: 'a,
    {
        let accumulators = accumulators.collect::<Vec<_>>();

        let mut combined_hp_inputs = Vec::new();
        for input in inputs {
            // Instantiate hp instances
            // TODO: Challenge
            let challenge = G::ScalarField::one();
            let predicate_instance = &input.instance;
            let first_round_message = &predicate_instance.first_round_message;

            let mut comm_1 = first_round_message.comm_a;
            let mut comm_2 = first_round_message.comm_b;
            let mut comm_3 = first_round_message.comm_c;

            if predicate_instance.make_zk {
                if let Some(comm_r_a) = first_round_message.comm_r_a.as_ref() {
                    comm_1 += comm_r_a.mul(challenge);
                }

                if let Some(comm_r_b) = first_round_message.comm_r_b.as_ref() {
                    comm_2 += comm_r_b.mul(challenge);
                }

                if let Some(comm_r_c) = first_round_message.comm_r_c.as_ref() {
                    comm_3 += comm_r_c.mul(challenge);
                }
            }

            let hp_instance = HPInputInstance {
                comm_1,
                comm_2,
                comm_3,
            };

            // Instantiate hp witnesses
            let predicate_witness = &input.witness;
            let second_round_message = &predicate_witness.second_round_message;
            let a_vec = matrix_vec_mul(&prover_key.a, second_round_message.blinded_witness.as_slice(), &[]);
            let b_vec = matrix_vec_mul(&prover_key.b, second_round_message.blinded_witness.as_slice(), &[]);

            let randomness = if predicate_witness.make_zk {
                let rand_1 = second_round_message.sigma_a.unwrap_or(G::ScalarField::zero());
                let rand_2 = second_round_message.sigma_b.unwrap_or(G::ScalarField::zero());
                let rand_3 = second_round_message.sigma_c.unwrap_or(G::ScalarField::zero());
                Some((rand_1, rand_2, rand_3))
            } else {
                None
            };

            let hp_witness = HPInputWitness {
                a_vec,
                b_vec,
                randomness
            };

            combined_hp_inputs.push(Input { instance: hp_instance, witness: hp_witness });
        }

        HPAidedAccumulationScheme::prove(&prover_key.ck, combined_hp_inputs.iter(), accumulators.iter().map(|acc|{
            Accumulator {
                instance: acc.instance.hp_instance,
                witness: acc.instance.hp_witness,
            }
        }))

        unimplemented!()
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
        unimplemented!()
    }

    fn decide(
        decider_key: &Self::DeciderKey,
        accumulator: &Accumulator<Self>,
    ) -> Result<bool, Self::Error> {
        unimplemented!()
    }
}
