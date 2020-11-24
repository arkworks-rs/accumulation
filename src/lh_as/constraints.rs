use ark_crypto_primitives::snark::BooleanInputVar;
use ark_ec::group::Group;
use ark_ec::AffineCurve;
use ark_ff::Field;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use std::marker::PhantomData;

pub type VerifierKeyVar<F> = F;

// Specialized for Pedersen commitments
pub struct InputInstanceVar<G, C, F>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    F: FieldVar<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
{
    pub commitment_var: C,
    pub point_var: F,
    pub eval_var: F,

    pub _affine: PhantomData<G>,
}

pub struct SingleProofVar<G, C, F>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    F: FieldVar<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
{
    pub witness_commitment_var: C,
    pub witness_eval_var: F,
    pub eval_var: F,

    pub _affine: PhantomData<G>,
}

pub type ProofVar<G, C, F> = Vec<SingleProofVar<G, C, F>>;

// TODO: Rename
pub struct VerifierConstraints<G, C, F>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    F: FieldVar<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
{
    pub _affine: PhantomData<G>,
    pub _curve: PhantomData<C>,
    pub _field: PhantomData<F>,
}

impl<G, C, F> VerifierConstraints<G, C, F>
where
    G: AffineCurve,
    C: CurveVar<G::Projective, <G::BaseField as Field>::BasePrimeField>,
    F: FieldVar<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
{
    fn compute_challenges<'a>(challenge: &F, num_challenges: usize) -> Vec<F> {
        let mut output = Vec::with_capacity(num_challenges);
        let mut cur_challenge = F::one();

        for _ in 0..num_challenges {
            output.push(cur_challenge.clone());
            cur_challenge *= challenge;
        }

        output
    }

    fn combine_commitments<'a>(
        commitments: impl IntoIterator<Item = (&'a F, &'a C)>,
    ) -> Result<C, SynthesisError> {
        let mut combined_commitment = C::zero();
        for (scalar, comm) in commitments {
            combined_commitment += &comm.scalar_mul_le(scalar.to_bits_le()?.iter())?;
        }

        Ok(combined_commitment)
    }

    fn verify<'a>(
        verifier_key_var: &VerifierKeyVar<F>,
        input_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C, F>>,
        accumulator_instance_vars: impl IntoIterator<Item = &'a InputInstanceVar<G, C, F>>,
        new_accumulator_instance_var: &InputInstanceVar<G, C, F>,
        proof_var: &ProofVar<G, C, F>,
    ) -> Result<Boolean<<G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let mut verify_result = Boolean::Constant(true);

        let mut commitments = Vec::new();
        for (input_instance_var, single_proof_var) in input_instance_vars
            .into_iter()
            .chain(accumulator_instance_vars)
            .zip(proof_var)
        {
            // TODO: Absorb into a sponge for challenge

            let eval_check_lhs: F =
                single_proof_var.eval_var.clone() - &input_instance_var.eval_var;
            let eval_check_rhs: F = (new_accumulator_instance_var.point_var.clone()
                - &input_instance_var.point_var)
                .mul(&single_proof_var.witness_eval_var);

            let eval_check = eval_check_lhs.is_eq(&eval_check_rhs)?;
            verify_result = verify_result.and(&eval_check)?;

            commitments.push(&input_instance_var.commitment);
        }

        // TODO: Replace with sponge output
        let challenge_point = F::one();
        verify_result = challenge_point.is_eq(&new_accumulator_instance_var.point_var)?;

        // TODO: Replace with sponge output
        let linear_combination_challenge = F::one();
        let linear_combination_challenges =
            Self::compute_challenges(linear_combination_challenge, commitments.len());

        let combined_eval = Self::combine_evaluations(
            proof_var
                .iter()
                .map(|p| &p.eval_var)
                .chain(proof_var.iter().map(|p| &p.witness_eval_var)),
            &linear_combination_challenges,
        );

        if !combined_eval.eq(&new_accumulator_instance.eval) {
            return Ok(false);
        }

        let combined_commitment = Self::combine_commitments(
            commitments
                .into_iter()
                .chain(proof.into_iter().map(|p| &p.witness_commitment)),
            linear_combination_challenge,
        );

        if !combined_commitment.eq(new_accumulator_instance.commitment.commitment()) {
            return Ok(false);
        }

        /*
        let mut challenge_point_sponge = S::new();
        challenge_point_sponge.absorb(verifier_key);

        let mut commitments = Vec::new();
        for (input_instance, p) in input_instances
            .into_iter()
            .chain(accumulator_instances)
            .zip(proof)
        {
            if input_instance.commitment.degree_bound().is_some() {
                return Ok(false);
            }

            absorb![
                    &mut challenge_point_sponge,
                    input_instance,
                    &to_bytes!(p.witness_commitment.commitment()).unwrap()
                ];

            let eval_check_lhs = p.eval - input_instance.eval;
            let eval_check_rhs = p
                .witness_eval
                .mul(new_accumulator_instance.point - &input_instance.point);

            if !eval_check_lhs.eq(&eval_check_rhs) {
                return Ok(false);
            }

            commitments.push(&input_instance.commitment);
        }

        let challenge_point = challenge_point_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();

        if !challenge_point.eq(&new_accumulator_instance.point) {
            return Ok(false);
        }

        let mut linear_combination_challenge_sponge = S::new();
        linear_combination_challenge_sponge.absorb(&challenge_point);

        for proof in proof {
            absorb![
                    &mut linear_combination_challenge_sponge,
                    &to_bytes!(&proof.eval, &proof.witness_eval).unwrap()
                ];
        }

        let linear_combination_challenge = linear_combination_challenge_sponge
            .squeeze_field_elements(1)
            .pop()
            .unwrap();


        Ok(true)
         */

        Ok(verify_result)
    }
}
