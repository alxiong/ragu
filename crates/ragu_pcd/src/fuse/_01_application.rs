//! Evaluate the [`Step`] circuit.
//!
//! This creates a witness for the step circuit given the two input [`Pcd`]s and
//! the step witness. This produces the [`proof::Application`] component of the
//! proof. The inputs are all consumed, and the `left` and `right` proofs are
//! returned to the caller along with the output data from the step circuit.

use core::any::TypeId;

use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_circuits::{CircuitExt, polynomials::Rank};
use ragu_core::{Error, Result};
use rand::CryptoRng;

use crate::{
    Application, Header, Pcd, Proof,
    header::Suffix,
    proof,
    step::{
        self, Step,
        internal::adapter::{Adapter, StepWithSuffixes},
        internal::rerandomize::Rerandomize,
    },
};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_application_proof<RNG: CryptoRng, S: Step<C> + 'static>(
        &self,
        rng: &mut RNG,
        step: &S,
        witness: S::Witness,
        left: Pcd<C, R, S::Left>,
        right: Pcd<C, R, S::Right>,
    ) -> Result<(
        Proof<C, R>,
        Proof<C, R>,
        proof::Application<C, R>,
        <S::Output as Header<C::CircuitField>>::Data,
        S::Aux,
    )> {
        let step_index = self
            .step_registry
            .get(&TypeId::of::<S>())
            .ok_or_else(|| Error::Initialization("step type not registered".into()))?;
        let left_suffix = self.suffix_for::<S::Left>()?;
        let right_suffix = self.suffix_for::<S::Right>()?;
        let output_suffix = self.suffix_for::<S::Output>()?;

        let wrapped = StepWithSuffixes {
            step,
            left_suffix,
            right_suffix,
            output_suffix,
        };
        let adapter = Adapter::<C, &S, R, HEADER_SIZE>::new(wrapped);
        let (trace, aux) = adapter.rx((left.data, right.data, witness))?;
        let circuit_index = step_index.circuit_index(self.num_application_steps)?;
        let rx = self.native_registry.assemble(&trace, circuit_index)?;
        let blind = C::CircuitField::random(&mut *rng);
        let commitment = rx.commit_to_affine(C::host_generators(self.params), blind);

        let ((left_header, right_header), output_data, step_aux) = aux;

        Ok((
            left.proof,
            right.proof,
            proof::Application {
                circuit_id: circuit_index,
                left_header: left_header.into_inner(),
                right_header: right_header.into_inner(),
                rx,
                blind,
                commitment,
            },
            output_data,
            step_aux,
        ))
    }

    /// Build the application proof component for rerandomization.
    ///
    /// Uses [`Rerandomize`] with uniform left encoding to ensure circuit
    /// uniformity across header types. The left header data is preserved
    /// as-is (pass-through).
    pub(crate) fn compute_rerandomize_application<RNG: CryptoRng, H: Header<C::CircuitField>>(
        &self,
        rng: &mut RNG,
        data: &H::Data,
        left_suffix: Suffix,
    ) -> Result<proof::Application<C, R>> {
        let circuit = Rerandomize::<C, H, R, HEADER_SIZE>::new(left_suffix, Suffix::internal(1));
        let circuit_index = step::Index::internal(step::InternalIndex::Rerandomize)
            .circuit_index(self.num_application_steps)?;

        let (trace, (left_header, right_header)) = circuit.rx(data.clone())?;
        let rx = self.native_registry.assemble(&trace, circuit_index)?;
        let blind = C::CircuitField::random(&mut *rng);
        let commitment = rx.commit_to_affine(C::host_generators(self.params), blind);

        Ok(proof::Application {
            circuit_id: circuit_index,
            left_header: left_header.into_inner(),
            right_header: right_header.into_inner(),
            rx,
            blind,
            commitment,
        })
    }
}
