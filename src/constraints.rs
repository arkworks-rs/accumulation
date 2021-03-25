use crate::AccumulationScheme;

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;

#[cfg(feature = "impl")]
use {crate::ConstraintF, ark_ec::AffineCurve, ark_nonnative_field::NonNativeFieldVar};

// Useful type alias for implementations.
#[cfg(feature = "impl")]
pub(crate) type NNFieldVar<G> = NonNativeFieldVar<<G as AffineCurve>::ScalarField, ConstraintF<G>>;

/// The verifier gadget of an [`AccumulationScheme`].
pub trait ASVerifierGadget<CF: PrimeField, AS: AccumulationScheme<CF>> {
    /// The key used to check that an accumulator was computed correctly from the inputs
    /// and old accumulators.
    /// The constraints equivalent of [`AccumulationScheme::VerifierKey`].
    type VerifierKey: AllocVar<AS::VerifierKey, CF>;

    /// The instance of the input that was accumulated.
    /// The constraints equivalent of [`AccumulationScheme::InputInstance`].
    type InputInstance: AllocVar<AS::InputInstance, CF>;

    /// The instance of the accumulator.
    /// The constraints equivalent of [`AccumulationScheme::AccumulatorInstance`].
    type AccumulatorInstance: AllocVar<AS::AccumulatorInstance, CF>;

    /// The proof attesting that an accumulator was properly computed.
    /// The constraints equivalent of [`AccumulationScheme::Proof`].
    type Proof: AllocVar<AS::Proof, CF>;

    /// Verifies that the new accumulator instance was computed properly from the input instances
    /// and old accumulator instances.
    /// The constraints equivalent of [`AccumulationScheme::verify`].
    fn verify<'a, S: CryptographicSponge<CF>, SV: CryptographicSpongeVar<CF, S>>(
        cs: ConstraintSystemRef<CF>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        old_accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: Option<SV>,
    ) -> Result<Boolean<CF>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a;
}

/// The verifier gadget of an [`AtomicAccumulationScheme`][crate::AtomicAccumulationScheme].
pub trait AtomicASVerifierGadget<CF: PrimeField, AS: AccumulationScheme<CF>>:
    ASVerifierGadget<CF, AS>
{
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ASVerifierGadget;
    use crate::tests::{ASTestInput, TestParameters};
    use crate::{AccumulationScheme, MakeZK};
    use ark_ff::PrimeField;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_sponge::constraints::CryptographicSpongeVar;
    use ark_sponge::CryptographicSponge;
    use ark_std::marker::PhantomData;

    pub struct ASVerifierGadgetTests<CF, AS, ASV, I, S, SV>
    where
        CF: PrimeField,
        AS: AccumulationScheme<CF>,
        ASV: ASVerifierGadget<CF, AS>,
        I: ASTestInput<CF, AS>,
        S: CryptographicSponge<CF>,
        SV: CryptographicSpongeVar<CF, S>,
    {
        _constraint_field: PhantomData<CF>,
        _test_input: PhantomData<I>,
        _acc_scheme: PhantomData<AS>,
        _acc_scheme_verifier: PhantomData<ASV>,
        _sponge: PhantomData<S>,
        _sponge_var: PhantomData<SV>,
    }

    impl<CF, AS, ASV, I, S, SV> ASVerifierGadgetTests<CF, AS, ASV, I, S, SV>
    where
        CF: PrimeField,
        AS: AccumulationScheme<CF>,
        ASV: ASVerifierGadget<CF, AS>,
        I: ASTestInput<CF, AS>,
        S: CryptographicSponge<CF>,
        SV: CryptographicSpongeVar<CF, S>,
    {
        pub fn test_initialization(test_params: &I::TestParams, num_iterations: usize) {
            let mut rng = ark_std::test_rng();
            for _ in 0..num_iterations {
                let (input_params, predicate_params, predicate_index) =
                    I::setup(test_params, &mut rng);
                let pp = AS::setup(&mut rng).unwrap();
                let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

                let mut input = I::generate_inputs(&input_params, 1, &mut rng);
                let input = input.pop().unwrap();

                let (accumulator, proof) = AS::prove(
                    &pk,
                    vec![input.as_ref()],
                    vec![],
                    if test_params.make_zk() { MakeZK::Enabled(&mut rng) } else { MakeZK::Disabled },
                    None::<S>,
                )
                .unwrap();

                let cs = ConstraintSystem::<CF>::new_ref();

                let vk_var = ASV::VerifierKey::new_constant(cs.clone(), vk.clone()).unwrap();

                let input_instance_var =
                    ASV::InputInstance::new_witness(cs.clone(), || Ok(input.instance)).unwrap();

                let accumulator_instance_var =
                    ASV::AccumulatorInstance::new_witness(cs.clone(), || Ok(accumulator.instance))
                        .unwrap();

                let proof_var = ASV::Proof::new_witness(cs.clone(), || Ok(proof)).unwrap();

                ASV::verify(
                    cs.clone(),
                    &vk_var,
                    vec![&input_instance_var],
                    vec![],
                    &accumulator_instance_var,
                    &proof_var,
                    None::<SV>,
                )
                .unwrap()
                .enforce_equal(&Boolean::TRUE)
                .unwrap();

                assert!(cs.is_satisfied().unwrap());
            }
        }

        pub fn test_simple_accumulation(test_params: &I::TestParams, num_iterations: usize) {
            let mut rng = ark_std::test_rng();
            for _ in 0..num_iterations {
                let (input_params, predicate_params, predicate_index) =
                    I::setup(test_params, &mut rng);
                let pp = AS::setup(&mut rng).unwrap();
                let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

                let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

                let old_input = inputs.pop().unwrap();
                let new_input = inputs.pop().unwrap();

                let (old_accumulator, _) = AS::prove(
                    &pk,
                    vec![old_input.as_ref()],
                    vec![],
                    if test_params.make_zk() { MakeZK::Enabled(&mut rng) } else { MakeZK::Disabled },
                    None::<S>,
                )
                .unwrap();

                let (new_accumulator, proof) = AS::prove(
                    &pk,
                    vec![new_input.as_ref()],
                    vec![old_accumulator.as_ref()],
                    if test_params.make_zk() { MakeZK::Enabled(&mut rng) } else { MakeZK::Disabled },
                    None::<S>,
                )
                .unwrap();

                let cs = ConstraintSystem::<CF>::new_ref();

                let vk_var = ASV::VerifierKey::new_constant(cs.clone(), vk.clone()).unwrap();

                let new_input_instance_var =
                    ASV::InputInstance::new_witness(cs.clone(), || Ok(new_input.instance)).unwrap();

                let old_accumulator_instance_var =
                    ASV::AccumulatorInstance::new_witness(cs.clone(), || {
                        Ok(old_accumulator.instance)
                    })
                    .unwrap();

                let new_accumulator_instance_var = ASV::AccumulatorInstance::new_input(
                    cs.clone(),
                    || Ok(new_accumulator.instance),
                )
                .unwrap();

                let proof_var = ASV::Proof::new_witness(cs.clone(), || Ok(proof)).unwrap();

                ASV::verify(
                    cs.clone(),
                    &vk_var,
                    vec![&new_input_instance_var],
                    vec![&old_accumulator_instance_var],
                    &new_accumulator_instance_var,
                    &proof_var,
                    None::<SV>,
                )
                .unwrap()
                .enforce_equal(&Boolean::TRUE)
                .unwrap();

                assert!(cs.is_satisfied().unwrap());
            }
        }

        pub fn print_costs_breakdown(test_params: &I::TestParams) {
            let mut rng = ark_std::test_rng();

            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let pp = AS::setup(&mut rng).unwrap();
            let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

            let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

            let old_input = inputs.pop().unwrap();
            let new_input = inputs.pop().unwrap();

            let (old_accumulator, _) = AS::prove(
                &pk,
                vec![old_input.as_ref()],
                vec![],
                if test_params.make_zk() { MakeZK::Enabled(&mut rng) } else { MakeZK::Disabled },
                None::<S>,
            )
            .unwrap();

            let (new_accumulator, proof) = AS::prove(
                &pk,
                vec![new_input.as_ref()],
                vec![old_accumulator.as_ref()],
                if test_params.make_zk() { MakeZK::Enabled(&mut rng) } else { MakeZK::Disabled },
                None::<S>,
            )
            .unwrap();

            let cs = ConstraintSystem::<CF>::new_ref();

            let start_cost = cs.num_constraints();
            let vk_var = ASV::VerifierKey::new_constant(cs.clone(), vk.clone()).unwrap();
            println!(
                "Cost of allocating vk {:?}",
                cs.num_constraints() - start_cost
            );

            let start_cost = cs.num_constraints();
            let new_input_instance_var =
                ASV::InputInstance::new_witness(cs.clone(), || Ok(new_input.instance)).unwrap();
            println!(
                "Cost of allocating input {:?}",
                cs.num_constraints() - start_cost
            );

            let start_cost = cs.num_constraints();
            let old_accumulator_instance_var =
                ASV::AccumulatorInstance::new_witness(cs.clone(), || Ok(old_accumulator.instance))
                    .unwrap();
            println!(
                "Cost of allocating old accumulator {:?}",
                cs.num_constraints() - start_cost
            );

            let start_cost = cs.num_constraints();
            let new_accumulator_instance_var =
                ASV::AccumulatorInstance::new_input(cs.clone(), || Ok(new_accumulator.instance))
                    .unwrap();
            println!(
                "Cost of allocating new accumulator {:?}",
                cs.num_constraints() - start_cost
            );

            let start_cost = cs.num_constraints();
            let proof_var = ASV::Proof::new_witness(cs.clone(), || Ok(proof)).unwrap();
            println!(
                "Cost of allocating proof {:?}",
                cs.num_constraints() - start_cost
            );

            let start_cost = cs.num_constraints();
            ASV::verify(
                cs.clone(),
                &vk_var,
                vec![&new_input_instance_var],
                vec![&old_accumulator_instance_var],
                &new_accumulator_instance_var,
                &proof_var,
                None::<SV>,
            )
            .unwrap()
            .enforce_equal(&Boolean::TRUE)
            .unwrap();
            println!("Cost of verify {:?}", cs.num_constraints() - start_cost);

            println!("Num constaints: {:}", cs.num_constraints());
            println!("Num instance: {:}", cs.num_instance_variables());
            println!("Num witness: {:}", cs.num_witness_variables());

            assert!(cs.is_satisfied().unwrap());
        }
    }
}
