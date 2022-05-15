use crate::{AccumulationScheme, AtomicAccumulationScheme};

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;

/// The verifier gadget of an [`AccumulationScheme`].
pub trait ASVerifierGadget<
    CF: PrimeField,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<CF, S>,
    AS: AccumulationScheme<CF, S>,
>
{
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
    fn verify<'a>(
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
pub trait AtomicASVerifierGadget<
    CF: PrimeField,
    S: CryptographicSponge,
    SV: CryptographicSpongeVar<CF, S>,
    AS: AtomicAccumulationScheme<CF, S>,
>: ASVerifierGadget<CF, S, SV, AS>
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
    use ark_relations::r1cs::{ConstraintLayer, ConstraintSystem, SynthesisError, TracingMode};
    use ark_sponge::constraints::CryptographicSpongeVar;
    use ark_sponge::CryptographicSponge;
    use ark_std::marker::PhantomData;
    use tracing_subscriber::prelude::__tracing_subscriber_SubscriberExt;

    pub const NUM_ITERATIONS: usize = 1;

    pub struct ASVerifierGadgetTests<CF, S, SV, AS, ASV, I>
    where
        CF: PrimeField,
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF, S>,
        AS: AccumulationScheme<CF, S>,
        ASV: ASVerifierGadget<CF, S, SV, AS>,
        I: ASTestInput<CF, S, AS>,
    {
        _constraint_field: PhantomData<CF>,
        _sponge: PhantomData<S>,
        _sponge_var: PhantomData<SV>,
        _acc_scheme: PhantomData<AS>,
        _acc_scheme_verifier: PhantomData<ASV>,
        _test_input: PhantomData<I>,
    }

    impl<CF, S, SV, AS, ASV, I> ASVerifierGadgetTests<CF, S, SV, AS, ASV, I>
    where
        CF: PrimeField,
        S: CryptographicSponge,
        SV: CryptographicSpongeVar<CF, S>,
        AS: AccumulationScheme<CF, S>,
        ASV: ASVerifierGadget<CF, S, SV, AS>,
        I: ASTestInput<CF, S, AS>,
    {
        /// For each iteration, runs the accumulation scheme for `num_accumulations` steps of
        /// proving and verifying.
        /// Assumes that all native AS operations work.
        pub fn test_template(
            template_params: &TemplateParams,
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<bool, SynthesisError> {
            // First, some boilerplat that helps with debugging
            let mut layer = ConstraintLayer::default();
            layer.mode = TracingMode::OnlyConstraints;
            let subscriber = tracing_subscriber::Registry::default().with(layer);
            tracing::subscriber::set_global_default(subscriber).unwrap();

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

            let inputs = I::generate_inputs(
                &input_params,
                total_num_inputs,
                &mut rng,
                S::new(sponge_params),
            );
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
                        Input::<CF, S, AS>::map_to_refs(inputs),
                        Accumulator::<CF, S, AS>::map_to_refs(&old_accumulators),
                        if test_params.make_zk() {
                            MakeZK::Enabled(&mut rng)
                        } else {
                            MakeZK::Disabled
                        },
                        Some(S::new(sponge_params)),
                    )
                    .ok()
                    .unwrap();

                    if !AS::verify(
                        &vk,
                        Input::<CF, S, AS>::instances(inputs),
                        Accumulator::<CF, S, AS>::instances(&old_accumulators),
                        &accumulator.instance,
                        &proof,
                        Some(S::new(sponge_params)),
                    )
                    .unwrap()
                    {
                        println!("{}", format!("Verify failed"));
                        return Ok(false);
                    }

                    let accumulator_instance_var =
                        ASV::AccumulatorInstance::new_input(cs.clone(), || {
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
                        Some(SV::new(cs.clone(), spongevar_params)),
                    )
                    .unwrap()
                    .enforce_equal(&Boolean::TRUE)
                    .unwrap();

                    if !cs.is_satisfied().unwrap() {
                        println!("=========================================================");
                        println!("Unsatisfied constraints:");
                        println!("{}", cs.which_is_unsatisfied().unwrap().unwrap());
                        println!("=========================================================");
                    }

                    assert!(cs.is_satisfied().unwrap(), "Verify Gadget failed.");

                    old_accumulator_instance_vars.push(
                        ASV::AccumulatorInstance::new_witness(cs.clone(), || {
                            Ok(accumulator.instance.clone())
                        })
                        .unwrap(),
                    );
                    old_accumulators.push(accumulator);
                }
            }

            Ok(true)
        }

        pub fn print_costs_breakdown(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) {
            let mut rng = ark_std::test_rng();

            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let pp = AS::setup(&mut rng).unwrap();
            let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

            let mut inputs = I::generate_inputs(&input_params, 2, &mut rng, S::new(sponge_params));

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
                Some(S::new(sponge_params)),
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
                Some(S::new(sponge_params)),
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
                Some(SV::new(cs.clone(), spongevar_params)),
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
        pub fn single_input_init_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1],
            };
            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params
            )?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator using multiple inputs.
        pub fn multiple_inputs_init_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![3],
            };
            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params,
            )?);
            Ok(())
        }

        /// Tests the accumulation of one input and one accumulator.
        pub fn simple_accumulation_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 1],
            };
            Self::print_costs_breakdown(test_params, sponge_params, spongevar_params);
            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params,
            )?);
            Ok(())
        }

        /// Tests the accumulation of multiple inputs and multiple accumulators.
        pub fn multiple_inputs_accumulation_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 1, 2, 3],
            };
            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params,
            )?);
            Ok(())
        }

        /// Tests the accumulation of multiple accumulators without any inputs.
        pub fn accumulators_only_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: NUM_ITERATIONS,
                num_inputs_per_iteration: vec![1, 0, 0, 0],
            };

            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params,
            )?);
            Ok(())
        }

        /// Tests the initialization of the first accumulator without any inputs.
        pub fn no_inputs_init_test(
            test_params: &I::TestParams,
            sponge_params: &S::Parameters,
            spongevar_params: &SV::Parameters,
        ) -> Result<(), SynthesisError> {
            let template_params = TemplateParams {
                num_iterations: 1,
                num_inputs_per_iteration: vec![0],
            };

            assert!(Self::test_template(
                &template_params,
                test_params,
                sponge_params,
                spongevar_params,
            )?);
            Ok(())
        }
    }
}
