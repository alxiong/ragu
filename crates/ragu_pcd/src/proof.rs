use arithmetic::Cycle;
use ff::Field;
use ragu_circuits::{
    CircuitExt,
    mesh::Mesh,
    polynomials::{Rank, structured},
};

use alloc::{vec, vec::Vec};
use core::marker::PhantomData;

use super::{
    header::Header,
    internal_circuits::{self, dummy},
};

/// Represents a recursive proof for the correctness of some computation.
pub struct Proof<C: Cycle, R: Rank> {
    pub(crate) preamble: PreambleProof<C, R>,
    pub(crate) application: ApplicationProof<C, R>,
    pub(crate) _marker: PhantomData<(C, R)>,
}

pub struct ApplicationProof<C: Cycle, R: Rank> {
    pub(crate) circuit_id: usize,
    pub(crate) left_header: Vec<C::CircuitField>,
    pub(crate) right_header: Vec<C::CircuitField>,
    pub(crate) rx: structured::Polynomial<C::CircuitField, R>,
    pub(crate) _marker: PhantomData<(C, R)>,
}

pub struct PreambleProof<C: Cycle, R: Rank> {
    pub(crate) preamble_rx: structured::Polynomial<C::CircuitField, R>,
    pub(crate) preamble_commitment: C::HostCurve,
    pub(crate) preamble_blind: C::CircuitField,
    pub(crate) nested_preamble_rx: structured::Polynomial<C::ScalarField, R>,
    pub(crate) nested_preamble_commitment: C::NestedCurve,
    pub(crate) nested_preamble_blind: C::ScalarField,
    pub(crate) _marker: PhantomData<(C, R)>,
}

impl<C: Cycle, R: Rank> Clone for Proof<C, R> {
    fn clone(&self) -> Self {
        Proof {
            preamble: self.preamble.clone(),
            application: self.application.clone(),
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, R: Rank> Clone for ApplicationProof<C, R> {
    fn clone(&self) -> Self {
        ApplicationProof {
            circuit_id: self.circuit_id,
            left_header: self.left_header.clone(),
            right_header: self.right_header.clone(),
            rx: self.rx.clone(),
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, R: Rank> Clone for PreambleProof<C, R> {
    fn clone(&self) -> Self {
        PreambleProof {
            preamble_rx: self.preamble_rx.clone(),
            preamble_commitment: self.preamble_commitment,
            preamble_blind: self.preamble_blind,
            nested_preamble_rx: self.nested_preamble_rx.clone(),
            nested_preamble_commitment: self.nested_preamble_commitment,
            nested_preamble_blind: self.nested_preamble_blind,
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, R: Rank> Proof<C, R> {
    /// Augment a recursive proof with some data, described by a [`Header`].
    pub fn carry<H: Header<C::CircuitField>>(self, data: H::Data<'_>) -> Pcd<'_, C, R, H> {
        Pcd { proof: self, data }
    }
}

/// Represents proof-carrying data, a recursive proof for the correctness of
/// some accompanying data.
pub struct Pcd<'source, C: Cycle, R: Rank, H: Header<C::CircuitField>> {
    /// The recursive proof for the accompanying data.
    pub proof: Proof<C, R>,

    /// Arbitrary data encoded into a [`Header`].
    pub data: H::Data<'source>,
}

impl<C: Cycle, R: Rank, H: Header<C::CircuitField>> Clone for Pcd<'_, C, R, H> {
    fn clone(&self) -> Self {
        Pcd {
            proof: self.proof.clone(),
            data: self.data.clone(),
        }
    }
}

pub fn trivial<C: Cycle, R: Rank, const HEADER_SIZE: usize>(
    num_application_steps: usize,
    mesh: &Mesh<'_, C::CircuitField, R>,
    params: &C,
) -> Proof<C, R> {
    use internal_circuits::stages;
    use ragu_circuits::staging::StageExt;

    // Preamble rx polynomial
    let preamble_rx =
        stages::native::preamble::Stage::<C, R>::rx(()).expect("preamble rx should not fail");
    let preamble_blind = C::CircuitField::ONE;
    let preamble_commitment = preamble_rx.commit(params.host_generators(), preamble_blind);

    // Nested preamble rx polynomial
    let nested_preamble_rx =
        stages::nested::preamble::Stage::<C::HostCurve, R>::rx(preamble_commitment)
            .expect("nested preamble rx should not fail");
    let nested_preamble_blind = C::ScalarField::ONE;
    let nested_preamble_commitment =
        nested_preamble_rx.commit(params.nested_generators(), nested_preamble_blind);

    // Application rx polynomial
    let application_rx = dummy::Circuit
        .rx((), mesh.get_key())
        .expect("should not fail")
        .0;

    Proof {
        preamble: PreambleProof {
            preamble_rx,
            preamble_commitment,
            preamble_blind,
            nested_preamble_rx,
            nested_preamble_commitment,
            nested_preamble_blind,
            _marker: PhantomData,
        },
        application: ApplicationProof {
            rx: application_rx,
            circuit_id: internal_circuits::index(num_application_steps, dummy::CIRCUIT_ID),
            left_header: vec![C::CircuitField::ZERO; HEADER_SIZE],
            right_header: vec![C::CircuitField::ZERO; HEADER_SIZE],
            _marker: PhantomData,
        },
        _marker: PhantomData,
    }
}
