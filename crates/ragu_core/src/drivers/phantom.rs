//! Zero-cost dummy [`Driver`] implementation for
//! [`PhantomData<F>`](core::marker::PhantomData).
//!
//! `PhantomData<F>` implements [`Driver`] with `Wire = ()` and `MaybeKind =
//! Empty`. All constraint methods are no-ops, and witness closures are never
//! called — the compiler dead-code eliminates them entirely.
//!
//! This exists for three reasons:
//!
//! 1. **Type-level [`GadgetKind`] extraction.** The `Kind!` macro uses
//!    `PhantomData<F>` as a universal dummy driver to satisfy the type system
//!    when extracting a gadget's driver-agnostic kind (e.g. `Kind![F;
//!    Boolean<'_, _>]` expands to `<Boolean<'static, PhantomData<F>> as
//!    Gadget<…>>::Kind`).
//!
//! 2. **Wire counting and stripping.** [`Gadget::num_wires()`] and
//!    [`Emulator::wires()`] use `PhantomData<F>` as a [`WireMap`] destination
//!    to count or extract wires without materializing a real driver.
//!
//! 3. **Testing.** Used as a lightweight [`WireMap`] destination in unit tests
//!    where no actual constraint system is needed.
//!
//! [`GadgetKind`]: crate::gadgets::GadgetKind
//! [`Gadget::num_wires()`]: crate::gadgets::Gadget::num_wires
//! [`Emulator::wires()`]: super::emulator::Emulator::wires
//! [`WireMap`]: crate::convert::WireMap

use super::{Coeff, Driver, DriverTypes, Field, Result};

/// Dummy driver that does absolutely nothing. All gates and constraints are
/// no-ops, and witness closures are dead-code eliminated via `MaybeKind =
/// Empty`.
impl<F: Field> Driver<'_> for core::marker::PhantomData<F> {
    type F = F;
    type Wire = ();
    const ONE: Self::Wire = ();

    fn mul(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Self::Wire, Self::Wire, Self::Wire)> {
        Ok(((), (), ()))
    }

    fn add(&mut self, _: impl Fn(Self::LCadd) -> Self::LCadd) -> Self::Wire {}

    fn enforce_zero(&mut self, _: impl Fn(Self::LCenforce) -> Self::LCenforce) -> Result<()> {
        Ok(())
    }
}

impl<F: Field> DriverTypes for core::marker::PhantomData<F> {
    type ImplField = F;
    type ImplWire = ();
    type MaybeKind = crate::maybe::Empty;
    type LCadd = ();
    type LCenforce = ();
}
