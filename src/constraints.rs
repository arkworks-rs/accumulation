use crate::{AccumulationScheme, AtomicAccumulationScheme};
use ark_ec::AffineCurve;
use ark_ff::{Field, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub type ConstraintF<G> = <<G as AffineCurve>::BaseField as Field>::BasePrimeField;
pub type NNFieldVar<G> = NonNativeFieldVar<<G as AffineCurve>::ScalarField, ConstraintF<G>>;

pub trait ASVerifierGadget<AS: AccumulationScheme, CF: PrimeField> {
    type VerifierKey: AllocVar<AS::VerifierKey, CF>;
    type InputInstance: AllocVar<AS::InputInstance, CF>;
    type AccumulatorInstance: AllocVar<AS::AccumulatorInstance, CF>;
    type Proof: AllocVar<AS::Proof, CF>;

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
        Self::AccumulatorInstance: 'a;
}

pub trait AtomicASVerifierGadget<AS: AtomicAccumulationScheme, CF: PrimeField>:
    ASVerifierGadget<AS, CF>
{
}

#[cfg(test)]
pub mod tests {
    use crate::constraints::ASVerifierGadget;
    use crate::tests::ASTestInput;
    use crate::AccumulationScheme;
    use ark_ff::PrimeField;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::bits::boolean::Boolean;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::{
        ConstraintLayer, ConstraintSystem, ConstraintSystemRef, TracingMode,
    };

    pub fn test_initialization<AS, I, CF, ASV>(test_params: &I::TestParams, num_iterations: usize)
    where
        AS: AccumulationScheme,
        I: ASTestInput<AS>,
        CF: PrimeField,
        ASV: ASVerifierGadget<AS, CF>,
    {
        let mut rng = ark_std::test_rng();
        for _ in 0..num_iterations {
            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let pp = AS::generate(&mut rng).unwrap();
            let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

            let mut input = I::generate_inputs(&input_params, 1, &mut rng);
            let input = input.pop().unwrap();

            let (accumulator, proof) =
                AS::prove(&pk, vec![input.as_ref()], vec![], Some(&mut rng)).unwrap();

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

    pub fn test_simple_accumulation<AS, I, CF, ASV>(
        test_params: &I::TestParams,
        num_iterations: usize,
    ) where
        AS: AccumulationScheme,
        I: ASTestInput<AS>,
        CF: PrimeField,
        ASV: ASVerifierGadget<AS, CF>,
    {
        let mut rng = ark_std::test_rng();
        for _ in 0..num_iterations {
            let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
            let pp = AS::generate(&mut rng).unwrap();
            let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

            let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

            let old_input = inputs.pop().unwrap();
            let new_input = inputs.pop().unwrap();

            let (old_accumulator, _) =
                AS::prove(&pk, vec![old_input.as_ref()], vec![], Some(&mut rng)).unwrap();

            let (new_accumulator, proof) = AS::prove(
                &pk,
                vec![new_input.as_ref()],
                vec![old_accumulator.as_ref()],
                Some(&mut rng),
            )
            .unwrap();

            let cs = ConstraintSystem::<CF>::new_ref();

            let vk_var = ASV::VerifierKey::new_constant(cs.clone(), vk.clone()).unwrap();

            let new_input_instance_var =
                ASV::InputInstance::new_witness(cs.clone(), || Ok(new_input.instance)).unwrap();

            let old_accumulator_instance_var =
                ASV::AccumulatorInstance::new_witness(cs.clone(), || Ok(old_accumulator.instance))
                    .unwrap();

            let new_accumulator_instance_var =
                ASV::AccumulatorInstance::new_input(cs.clone(), || Ok(new_accumulator.instance))
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

    pub fn print_costs_breakdown<AS, I, CF, ASV>(test_params: &I::TestParams)
    where
        AS: AccumulationScheme,
        I: ASTestInput<AS>,
        CF: PrimeField,
        ASV: ASVerifierGadget<AS, CF>,
    {
        let mut rng = ark_std::test_rng();

        let (input_params, predicate_params, predicate_index) = I::setup(test_params, &mut rng);
        let pp = AS::generate(&mut rng).unwrap();
        let (pk, vk, _) = AS::index(&pp, &predicate_params, &predicate_index).unwrap();

        let mut inputs = I::generate_inputs(&input_params, 2, &mut rng);

        let old_input = inputs.pop().unwrap();
        let new_input = inputs.pop().unwrap();

        let (old_accumulator, _) =
            AS::prove(&pk, vec![old_input.as_ref()], vec![], Some(&mut rng)).unwrap();

        let (new_accumulator, proof) = AS::prove(
            &pk,
            vec![new_input.as_ref()],
            vec![old_accumulator.as_ref()],
            Some(&mut rng),
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
