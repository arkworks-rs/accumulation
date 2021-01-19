use ark_ec::AffineCurve;
use ark_ff::{to_bytes, PrimeField};
use ark_relations::r1cs::ToConstraintField;
use ark_sponge::Absorbable;
use ark_std::slice::SliceIndex;

pub struct InputInstance<G: AffineCurve> {
    pub comm_1: G,
    pub comm_2: G,
    pub comm_3: G,
}

impl<G, CF> Absorbable<CF> for InputInstance<G>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![self.comm_1, self.comm_2, self.comm_3].unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output: Vec<CF> = self.comm_1.to_field_elements().unwrap();
        output.append(&mut self.comm_2.to_field_elements().unwrap());
        output.append(&mut self.comm_3.to_field_elements().unwrap());
        output
    }
}

pub struct InputWitness<G: AffineCurve> {
    pub a_vec: Vec<G::ScalarField>,
    pub b_vec: Vec<G::ScalarField>,
    // TODO: Add hiding
    //pub randomness: Option<(G::ScalarField, G::ScalarField, G::ScalarField)>,
}

pub struct Proof<G: AffineCurve> {
    pub t_comms: (Vec<G>, Vec<G>),
}

impl<G, CF> Absorbable<CF> for Proof<G>
where
    G: AffineCurve + ToConstraintField<CF>,
    CF: PrimeField,
{
    // TODO: Absorb size?
    fn to_sponge_bytes(&self) -> Vec<u8> {
        let mut bytes = to_bytes!(self.t_comms.0).unwrap();
        bytes.append(&mut to_bytes!(self.t_comms.1).unwrap());
        bytes
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output: Vec<CF> = Vec::new();
        for t_comm in &self.t_comms.0 {
            output.append(&mut t_comm.to_field_elements().unwrap())
        }

        for t_comm in &self.t_comms.1 {
            output.append(&mut t_comm.to_field_elements().unwrap())
        }
        output
    }
}
