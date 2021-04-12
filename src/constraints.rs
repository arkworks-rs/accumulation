use crate::AccumulationScheme;

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;

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
    use crate::tests::{ASTestInput, TemplateParams, TestParameters};
    use crate::{AccumulationScheme, Accumulator, Input, MakeZK};
    use ark_ff::PrimeField;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
    use ark_sponge::constraints::CryptographicSpongeVar;
    use ark_sponge::CryptographicSponge;
    use ark_std::marker::PhantomData;

    pub const NUM_ITERATIONS: usize = 1;

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
        /// For each iteration, runs the accumulation scheme for `num_accumulations` steps of
        /// proving and verifying.
        /// Assumes that all native AS operations work.
        pub fn test_template(
            template_params: &TemplateParams,
            test_params: &I::TestParams,
        ) -> Result<bool, SynthesisError> {
            assert!(template_params.num_iterations > 0);

            let num_inputs_per_iteration = &template_params.num_inputs_per_iteration;
            let num_iterations = template_params.num_iterations;
            let total_num_inputs = num_iterations * num_inputs_per_iteration.iter().sum::<usize>();

            let cs = ConstraintSystem::<CF>::new_ref();

            let mut rng = ark_std::test_rng();
            let public_params = AS::setup(&mut rng).ok().unwrap();

            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let (pk, vk, _) = AS::index(&public_params, &predicate_params, &predicate_index)
                .ok()
                .unwrap();
            let vk_var = ASV::VerifierKey::new_constant(cs.clone(), vk.clone())?;

            let inputs = I::generate_inputs(&input_params, total_num_inputs, &mut rng);
            assert_eq!(total_num_inputs, inputs.len());

            let input_instance_vars = inputs
                .iter()
                .map(|input| {
                    ASV::InputInstance::new_witness(cs.clone(), || Ok(input.instance.clone()))
                })
                .collect::<Result<Vec<_>, SynthesisError>>()
                .unwrap();

            let mut inputs_start = 0;
            for _ in 0..num_iterations {
                let mut old_accumulators = Vec::with_capacity(num_inputs_per_iteration.len());
                let mut old_accumulator_instance_vars =
                    Vec::with_capacity(num_inputs_per_iteration.len());

                for num_inputs in num_inputs_per_iteration {
                    let inputs = &inputs[inputs_start..(inputs_start + num_inputs)];
                    let input_instance_vars =
                        &input_instance_vars[inputs_start..(inputs_start + num_inputs)];
                    inputs_start += num_inputs;

                    let (accumulator, proof) = AS::prove(
                        &pk,
                        Input::<CF, AS>::map_to_refs(inputs),
                        Accumulator::<CF, AS>::map_to_refs(&old_accumulators),
                        if test_params.make_zk() {
                            MakeZK::Enabled(&mut rng)
                        } else {
                            MakeZK::Disabled
                        },
                        None::<S>,
                    )
                    .ok()
                    .unwrap();

                    let accumulator_instance_var =
                        ASV::AccumulatorInstance::new_witness(cs.clone(), || {
                            Ok(accumulator.instance.clone())
                        })
                        .unwrap();

                    let proof_var = ASV::Proof::new_witness(cs.clone(), || Ok(proof)).unwrap();

                    assert!(
                        cs.is_satisfied().unwrap(),
                        "CS is not satisfied from the test setup."
                    );

                    ASV::verify(
                        cs.clone(),
                        &vk_var,
                        input_instance_vars,
                        &old_accumulator_instance_vars,
                        &accumulator_instance_var,
                        &proof_var,
                        None::<SV>,
                    )
                    .unwrap()
                    .enforce_equal(&Boolean::TRUE)
                    .unwrap();

                    assert!(cs.is_satisfied().unwrap(), "Verify failed.");

                    old_accumulators.push(accumulator);
                    old_accumulator_instance_vars.push(accumulator_instance_var);
                }
            }

            Ok(true)
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
                if test_params.make_zk() {
                    MakeZK::Enabled(&mut rng)
                } else {
                    MakeZK::Disabled
                },
                None::<S>,
            )
            .unwrap();

            let (new_accumulator, proof) = AS::prove(
                &pk,
                vec![new_input.as_ref()],
                vec![old_accumulator.as_ref()],
                if test_params.make_zk() {
                    MakeZK::Enabled(&mut rng)
                } else {
                    MakeZK::Disabled
                },
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

        /// Tests the initialization of the first accumulator using one input.
        pub fn single_input_init_test(test_params: &I::TestParams) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator using multiple inputs.
        pub fn multiple_inputs_init_test(
            test_params: &I::TestParams,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![3],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of one input and one accumulator.
        pub fn simple_accumulation_test(test_params: &I::TestParams) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1; 2],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of three inputs and three accumulators.
        pub fn multiple_inputs_accumulation_test(
            test_params: &I::TestParams,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![3; 4],
            };
            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the accumulation of three accumulators only.
        pub fn accumulators_only_test(test_params: &I::TestParams) -> Result<(), SynthesisError> {
            let mut num_inputs_per_iteration = vec![0; 4];

            // To initialize the starting accumulator
            num_inputs_per_iteration[0] = 1;

            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration,
            };

            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator using no inputs.
        pub fn no_inputs_init_test(test_params: &I::TestParams) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: 1,
                num_inputs_per_iteration: vec![0],
            };

            assert!(Self::test_template(&template_params, test_params)?);
            Ok(())
        }
    }
}
