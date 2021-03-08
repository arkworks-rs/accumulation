use crate::{AccumulationScheme, AtomicAccumulationScheme};
use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;

pub type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
pub type NNFieldVar<G> = NonNativeFieldVar<<G as AffineCurve>::ScalarField, ConstraintF<G>>;

pub trait ASVerifierGadget<
    CF: PrimeField,
    S: CryptographicSponge<CF>,
    SV: CryptographicSpongeVar<CF, S>,
    AS: AccumulationScheme<CF, S>,
>
{
    type VerifierKey: AllocVar<AS::VerifierKey, CF>;
    type InputInstance: AllocVar<AS::InputInstance, CF>;
    type AccumulatorInstance: AllocVar<AS::AccumulatorInstance, CF>;
    type Proof: AllocVar<AS::Proof, CF>;

    fn verify_with_sponge<'a>(
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
        sponge: SV,
    ) -> Result<Boolean<CF>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a;

    fn verify<'a>(
        cs: ConstraintSystemRef<CF>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<Boolean<CF>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        Self::verify_with_sponge(
            verifier_key,
            input_instances,
            accumulator_instances,
            new_accumulator_instance,
            proof,
            SV::new(cs),
        )
    }
}

pub trait AtomicASVerifierGadget<
    CF: PrimeField,
    S: CryptographicSponge<CF>,
    SV: CryptographicSpongeVar<CF, S>,
    AS: AccumulationScheme<CF, S>,
>: ASVerifierGadget<CF, S, SV, AS>
{
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ASVerifierGadget;
    use crate::tests::ASTestInput;
    use crate::{AccumulationScheme, MakeZK};
    use ark_ff::PrimeField;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::{
        ConstraintLayer, ConstraintSystem, ConstraintSystemRef, TracingMode,
    };
    use ark_sponge::constraints::CryptographicSpongeVar;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::CryptographicSponge;
    use std::marker::PhantomData;

    pub struct ASVerifierGadgetTests<CF, S, SV, AS, ASV, I>
    where
        CF: PrimeField,
        S: CryptographicSponge<CF>,
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
        S: CryptographicSponge<CF>,
        SV: CryptographicSpongeVar<CF, S>,
        AS: AccumulationScheme<CF, S>,
        ASV: ASVerifierGadget<CF, S, SV, AS>,
        I: ASTestInput<CF, S, AS>,
    {
        pub fn test_initialization(test_params: &I::TestParams, num_iterations: usize) {
            let mut rng = ark_std::test_rng();
            for _ in 0..num_iterations {
                let (input_params, predicate_params, predicate_index) =
                    I::setup(test_params, &mut rng);
                let pp = AS::generate(&mut rng).unwrap();
                let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

                let mut input = I::generate_inputs(&input_params, 1, &mut rng);
                let input = input.pop().unwrap();

                let (accumulator, proof) = AS::prove(
                    &pk,
                    vec![input.as_ref()],
                    vec![],
                    MakeZK::Inherited(Some(&mut rng)),
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
                let pp = AS::generate(&mut rng).unwrap();
                let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

                let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

                let old_input = inputs.pop().unwrap();
                let new_input = inputs.pop().unwrap();

                let (old_accumulator, _) = AS::prove(
                    &pk,
                    vec![old_input.as_ref()],
                    vec![],
                    MakeZK::Inherited(Some(&mut rng)),
                )
                .unwrap();

                let (new_accumulator, proof) = AS::prove(
                    &pk,
                    vec![new_input.as_ref()],
                    vec![old_accumulator.as_ref()],
                    MakeZK::Inherited(Some(&mut rng)),
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
            let pp = AS::generate(&mut rng).unwrap();
            let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

            let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

            let old_input = inputs.pop().unwrap();
            let new_input = inputs.pop().unwrap();

            let (old_accumulator, _) = AS::prove(
                &pk,
                vec![old_input.as_ref()],
                vec![],
                MakeZK::Inherited(Some(&mut rng)),
            )
            .unwrap();

            let (new_accumulator, proof) = AS::prove(
                &pk,
                vec![new_input.as_ref()],
                vec![old_accumulator.as_ref()],
                MakeZK::Inherited(Some(&mut rng)),
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
