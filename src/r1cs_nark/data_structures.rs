use ark_ec::AffineCurve;
use ark_ff::{to_bytes, Field, PrimeField};
use ark_poly_commit::pedersen::*;
use ark_relations::r1cs::{Matrix, ToConstraintField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::Absorbable;
use ark_std::io::{Read, Write};

/// The public parameters of this NARK.
pub type PublicParameters = ();

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Clone, Copy)]
pub struct IndexInfo {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The number of public input (i.e. instance) variables.
    pub num_instance_variables: usize,
    /// Hash of the matrices.
    pub matrices_hash: [u8; 32],
}

/// The index prover key for our NARK.
#[derive(Clone)]
pub struct IndexProverKey<G: AffineCurve> {
    /// Information about the index.
    pub index_info: IndexInfo,

    /// The A matrix for the R1CS instance.
    pub a: Matrix<G::ScalarField>,
    /// The B matrix for the R1CS instance.
    pub b: Matrix<G::ScalarField>,
    /// The C matrix for the R1CS instance.
    pub c: Matrix<G::ScalarField>,

    /// The group elements required by the Pedersen commitment.
    pub ck: CommitterKey<G>,
}

/// Index verifier key for our NARK.
pub type IndexVerifierKey<G> = IndexProverKey<G>;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct FirstRoundMessage<G: AffineCurve> {
    pub comm_a: G,
    pub comm_b: G,
    pub comm_c: G,
    pub comm_r_a: Option<G>,
    pub comm_r_b: Option<G>,
    pub comm_r_c: Option<G>,
    pub comm_1: Option<G>,
    pub comm_2: Option<G>,
}

impl<CF, G> Absorbable<CF> for FirstRoundMessage<G>
where
    CF: PrimeField,
    G: AffineCurve + ToConstraintField<CF>,
{
    fn to_sponge_bytes(&self) -> Vec<u8> {
        to_bytes![
            self.comm_a,
            self.comm_b,
            self.comm_c,
            self.comm_r_a,
            self.comm_r_b,
            self.comm_r_c,
            self.comm_1,
            self.comm_2
        ]
        .unwrap()
    }

    fn to_sponge_field_elements(&self) -> Vec<CF> {
        let mut output = self.comm_a.to_field_elements().unwrap();
        output.append(&mut self.comm_b.to_field_elements().unwrap());
        output.append(&mut self.comm_c.to_field_elements().unwrap());

        for comm in [
            self.comm_r_a.as_ref(),
            self.comm_r_b.as_ref(),
            self.comm_r_c.as_ref(),
            self.comm_1.as_ref(),
            self.comm_2.as_ref(),
        ]
        .iter()
        {
            if let Some(comm) = comm {
                output.push(CF::one());
                output.append(&mut comm.to_field_elements().unwrap());
            } else {
                output.push(CF::zero());
            }
        }
        output
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SecondRoundMessage<F: Field> {
    pub blinded_witness: Vec<F>,
    pub sigma_a: Option<F>,
    pub sigma_b: Option<F>,
    pub sigma_c: Option<F>,
    pub sigma_o: Option<F>,
}

/// The proof for our NARK.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<G: AffineCurve> {
    pub first_msg: FirstRoundMessage<G>,
    pub second_msg: SecondRoundMessage<G::ScalarField>,
    pub make_zk: bool,
}
