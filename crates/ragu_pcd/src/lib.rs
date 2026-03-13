//! # `ragu_pcd`

#![no_std]
#![allow(clippy::type_complexity, clippy::too_many_arguments)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![doc(html_favicon_url = "https://tachyon.z.cash/assets/ragu/v1/favicon-32x32.png")]
#![doc(html_logo_url = "https://tachyon.z.cash/assets/ragu/v1/rustdoc-128x128.png")]

extern crate alloc;
#[cfg(feature = "multicore")]
extern crate std;

mod circuits;
mod components;
mod fuse;
pub mod header;
mod proof;
pub mod step;
mod verify;

use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::Rank,
    registry::{Registry, RegistryBuilder},
};
use ragu_core::{Error, Result};
use rand::CryptoRng;

use alloc::{collections::BTreeMap, sync::Arc};
use core::{any::TypeId, cell::OnceCell, marker::PhantomData};

use header::{Header, Suffix};
pub use proof::{Pcd, Proof};
use step::{
    Step,
    internal::adapter::{Adapter, StepWithSuffixes},
    internal::rerandomize::Rerandomize,
};

/// Domain separation tag for Ragu PCD protocol.
// FIXME: choose a permanent domain separation tag before release.
pub(crate) const RAGU_TAG: &[u8] = b"FIXME";

/// Builder for an [`Application`] for proof-carrying data.
pub struct ApplicationBuilder<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize> {
    native_registry: RegistryBuilder<'params, C::CircuitField, R>,
    nested_registry: RegistryBuilder<'params, C::ScalarField, R>,
    num_application_steps: usize,
    // map Header types to their assigned suffixes
    suffix_registry: BTreeMap<TypeId, Suffix>,
    // map Step types to their assigned step indices
    step_registry: BTreeMap<TypeId, step::Index>,
    _marker: PhantomData<[(); HEADER_SIZE]>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Default
    for ApplicationBuilder<'_, C, R, HEADER_SIZE>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize>
    ApplicationBuilder<'params, C, R, HEADER_SIZE>
{
    /// Create an empty [`ApplicationBuilder`] for proof-carrying data.
    pub fn new() -> Self {
        let mut suffix_registry = BTreeMap::new();
        // Pre-register the trivial header `()` with its internal suffix.
        suffix_registry.insert(TypeId::of::<()>(), Suffix::internal(1));

        ApplicationBuilder {
            native_registry: RegistryBuilder::new(),
            nested_registry: RegistryBuilder::new(),
            num_application_steps: 0,
            suffix_registry,
            step_registry: BTreeMap::new(),
            _marker: PhantomData,
        }
    }

    /// Register a step type.
    ///
    /// Each concrete step type may only be registered once. Use newtypes to
    /// register multiple configurations of the same logic.
    ///
    /// Returns `self` for chaining.
    pub fn register<S>(mut self, step: S) -> Result<Self>
    where
        S: Step<C> + 'static,
    {
        let type_id = TypeId::of::<S>();
        if self.step_registry.contains_key(&type_id) {
            return Err(Error::Initialization("step type already registered".into()));
        }

        let wrapped = StepWithSuffixes {
            step,
            left_suffix: self.assign_suffix::<S::Left>(),
            right_suffix: self.assign_suffix::<S::Right>(),
            output_suffix: self.assign_suffix::<S::Output>(),
        };

        self.native_registry =
            self.native_registry
                .register_circuit(Adapter::<C, S, R, HEADER_SIZE>::new(wrapped))?;
        self.step_registry
            .insert(type_id, step::Index::new(self.num_application_steps));
        self.num_application_steps += 1;

        Ok(self)
    }

    /// Register `count` trivial circuits to simulate application steps
    /// registration.
    ///
    /// This is useful for testing internal circuit behavior with a non-zero
    /// number of application steps, without needing real [`Step`]
    /// implementations.
    #[cfg(test)]
    pub(crate) fn register_dummy_circuits(mut self, count: usize) -> Result<Self> {
        for _ in 0..count {
            self.native_registry = self.native_registry.register_circuit(())?;
            self.num_application_steps += 1;
        }
        Ok(self)
    }

    /// Returns the assigned suffix for the header type, assigning a new one
    /// if unassigned yet.
    fn assign_suffix<H: Header<C::CircuitField>>(&mut self) -> Suffix {
        let next_suffix = self
            .suffix_registry
            .values()
            .filter(|s| !s.is_internal())
            .count();
        *self
            .suffix_registry
            .entry(TypeId::of::<H>())
            .or_insert_with(|| Suffix::new(next_suffix))
    }

    /// Perform finalization and optimization steps to produce the
    /// [`Application`].
    pub fn finalize(
        mut self,
        params: &'params C::Params,
    ) -> Result<Application<'params, C, R, HEADER_SIZE>> {
        // Build the native registry:
        // 1. Internal masks
        // 2. Internal circuits
        // 3. Internal steps
        // 4. Application circuits (already registered)
        let (total_circuits, log2_circuits) =
            circuits::native::total_circuit_counts(self.num_application_steps);

        // First, register internal masks and circuits
        self.native_registry = circuits::native::register_all::<C, R, HEADER_SIZE>(
            self.native_registry,
            params,
            log2_circuits,
        )?;

        // Then, register internal slots (rerandomize circuit + trivial step).
        // Rerandomize uses `()` as header type for registration — uniform
        // encoding ensures circuit uniformity regardless of the actual header
        // type used at runtime.
        self.native_registry =
            self.native_registry.register_internal_circuit(
                Rerandomize::<C, (), R, HEADER_SIZE>::new(Suffix::internal(1), Suffix::internal(1)),
            )?;
        self.native_registry =
            self.native_registry.register_internal_circuit(
                Adapter::<C, _, R, HEADER_SIZE>::new(StepWithSuffixes {
                    step: step::internal::trivial::Trivial::new(),
                    left_suffix: Suffix::internal(1),
                    right_suffix: Suffix::internal(1),
                    output_suffix: Suffix::internal(1),
                }),
            )?;

        // Register Trivial in step_registry so it can be used via
        // seed()/fuse(). Rerandomize is not a Step — it bypasses fuse
        // entirely via Application::rerandomize().
        self.step_registry.insert(
            TypeId::of::<step::internal::trivial::Trivial>(),
            step::Index::internal(step::InternalIndex::Trivial),
        );

        assert_eq!(
            self.native_registry.log2_circuits(),
            log2_circuits,
            "log2_circuits mismatch"
        );
        assert_eq!(
            self.native_registry.num_circuits(),
            total_circuits,
            "final circuit count mismatch"
        );

        // Register nested internal circuits (no application steps, no headers).
        self.nested_registry = circuits::nested::register_all::<C, R>(self.nested_registry)?;

        Ok(Application {
            native_registry: self.native_registry.finalize()?,
            nested_registry: self.nested_registry.finalize()?,
            params,
            num_application_steps: self.num_application_steps,
            suffix_registry: self.suffix_registry,
            step_registry: self.step_registry,
            seeded_trivial: OnceCell::new(),
            _marker: PhantomData,
        })
    }
}

/// The recursion context that is used to create and verify proof-carrying data.
pub struct Application<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize> {
    native_registry: Registry<'params, C::CircuitField, R>,
    nested_registry: Registry<'params, C::ScalarField, R>,
    params: &'params C::Params,
    num_application_steps: usize,
    suffix_registry: BTreeMap<TypeId, Suffix>,
    step_registry: BTreeMap<TypeId, step::Index>,
    /// Cached seeded trivial proof for rerandomization.
    seeded_trivial: OnceCell<Proof<C, R>>,
    _marker: PhantomData<[(); HEADER_SIZE]>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    /// Seed a new computation by running a step with trivial inputs.
    ///
    /// This is the entry point for creating leaf nodes in a PCD tree.
    /// Internally creates minimal trivial proofs with `()` headers and fuses
    /// them with the provided step to produce a valid proof.
    pub fn seed<RNG: CryptoRng, S: Step<C, Left = (), Right = ()> + 'static>(
        &self,
        rng: &mut RNG,
        step: &S,
        witness: S::Witness,
    ) -> Result<(Pcd<C, R, S::Output>, S::Aux)> {
        self.fuse(rng, step, witness, self.trivial_pcd(), self.trivial_pcd())
    }

    /// Returns a seeded trivial proof for use in rerandomization.
    ///
    /// A seeded trivial is a trivial proof that has been through `seed()`
    /// (folded with itself). This gives it valid proof structure, avoiding
    /// base case detection issues.
    ///
    /// The proof is lazily created on first use and cached. *Importantly*,
    /// note that this may return the same proof on subsequent calls, and
    /// is not random.
    fn seeded_trivial_pcd<RNG: CryptoRng>(&self, rng: &mut RNG) -> Pcd<C, R, ()> {
        self.seeded_trivial
            .get_or_init(|| {
                self.seed(rng, &step::internal::trivial::Trivial::new(), ())
                    .expect("seeded trivial seed should not fail")
                    .0
                    .proof
            })
            .clone()
            .carry(())
    }

    /// Rerandomize proof-carrying data.
    ///
    /// This will internally fold the [`Pcd`] with a seeded trivial proof
    /// using the rerandomize circuit, such that the resulting proof is valid
    /// for the same [`Header`] but reveals nothing else about the original
    /// proof. As a result, [`Application::verify`] should produce the same
    /// result on the provided `pcd` as it would the output of this method.
    pub fn rerandomize<RNG: CryptoRng, H: Header<C::CircuitField> + 'static>(
        &self,
        pcd: Pcd<C, R, H>,
        rng: &mut RNG,
    ) -> Result<Pcd<C, R, H>> {
        let seeded_trivial = self.seeded_trivial_pcd(rng);
        let left_suffix = self.suffix_for::<H>()?;
        let application =
            self.compute_rerandomize_application::<_, H>(rng, &pcd.data, left_suffix)?;

        let left = Arc::new(pcd.proof);
        let right = Arc::new(seeded_trivial.proof);
        let proof = self.fuse_with(rng, &left, &right, application)?;
        Ok(proof.carry(pcd.data))
    }

    /// Look up the suffix for a registered header type.
    pub(crate) fn suffix_for<H: Header<C::CircuitField>>(&self) -> Result<Suffix> {
        self.suffix_registry
            .get(&TypeId::of::<H>())
            .copied()
            .ok_or_else(|| Error::Initialization("header type not registered".into()))
    }
}
