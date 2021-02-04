use crate::constraints::{AidedAccumulationSchemeVerifierGadget, ConstraintF};
use crate::r1cs_nark_as::SimpleNARKVerifierAidedAccumulationScheme;
use crate::AidedAccumulationScheme;
use ark_ec::AffineCurve;
use ark_ff::ToConstraintField;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::groups::CurveVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::{Absorbable, CryptographicSponge};

pub mod data_structures;
use data_structures::*;
use std::marker::PhantomData;

pub struct SimpleNARKVerifierAidedAccumulationSchemeVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    C: CurveVar<G::Projective, ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    _affine_phantom: PhantomData<G>,
    _curve_phantom: PhantomData<C>,
    _sponge_phantom: PhantomData<SV>,
}

impl<G, S, CS, C, SV>
    AidedAccumulationSchemeVerifierGadget<
        SimpleNARKVerifierAidedAccumulationScheme<G, S, CS>,
        ConstraintF<G>,
    > for SimpleNARKVerifierAidedAccumulationSchemeVerifierGadget<G, C, SV>
where
    G: AffineCurve + ToConstraintField<ConstraintF<G>>,
    ConstraintF<G>: Absorbable<ConstraintF<G>>,
    Vec<ConstraintF<G>>: Absorbable<ConstraintF<G>>,
    S: CryptographicSponge<ConstraintF<G>>,
    CS: ConstraintSynthesizer<G::ScalarField> + Clone,
    C: CurveVar<G::Projective, ConstraintF<G>>,
    SV: CryptographicSpongeVar<ConstraintF<G>>,
{
    type VerifierKey = VerifierKeyVar<ConstraintF<G>>;
    type InputInstance = InputInstanceVar<G, C>;
    type AccumulatorInstance = AccumulatorInstanceVar<G, C>;
    type Proof = ProofVar<G, C>;

    fn verify<'a>(
        cs: ConstraintSystemRef<ConstraintF<G>>,
        verifier_key: &Self::VerifierKey,
        input_instances: impl IntoIterator<Item = &'a Self::InputInstance>,
        accumulator_instances: impl IntoIterator<Item = &'a Self::AccumulatorInstance>,
        new_accumulator_instance: &Self::AccumulatorInstance,
        proof: &Self::Proof,
    ) -> Result<Boolean<ConstraintF<G>>, SynthesisError>
    where
        Self::InputInstance: 'a,
        Self::AccumulatorInstance: 'a,
    {
        unimplemented!()
    }
}

#[cfg(test)]
pub mod tests {
    use crate::r1cs_nark::test::DummyCircuit;
    use crate::r1cs_nark_as::constraints::SimpleNARKVerifierAidedAccumulationSchemeVerifierGadget;
    use crate::r1cs_nark_as::tests::SimpleNARKVerifierAidedAccumulationSchemeTestInput;
    use crate::r1cs_nark_as::SimpleNARKVerifierAidedAccumulationScheme;
    use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_sponge::poseidon::PoseidonSponge;

    //type G = ark_pallas::Affine;
    //type C = ark_pallas::constraints::GVar;
    //type F = ark_pallas::Fr;
    //type ConstraintF = ark_pallas::Fq;
    type G = ark_ed_on_bls12_381::EdwardsAffine;
    type C = ark_ed_on_bls12_381::constraints::EdwardsVar;
    type F = ark_ed_on_bls12_381::Fr;
    type ConstraintF = ark_ed_on_bls12_381::Fq;

    type Sponge = PoseidonSponge<ConstraintF>;
    type SpongeVar = PoseidonSpongeVar<ConstraintF>;

    type Circuit = DummyCircuit<F>;

    type AS = SimpleNARKVerifierAidedAccumulationScheme<G, Sponge, Circuit>;
    type I = SimpleNARKVerifierAidedAccumulationSchemeTestInput;
    type ASV = SimpleNARKVerifierAidedAccumulationSchemeVerifierGadget<G, C, SpongeVar>;

    #[test]
    pub fn basic_test() {
        crate::constraints::tests::basic_test::<AS, I, ConstraintF, ASV>(&false, 1);
    }
}
