//! [`Write`] implementations for foreign standard library types.
//!
//! Enables types like `()`, arrays, tuples, and `Box<T>` to participate in
//! the circuit IO system by implementing the [`Write`] trait.

use ff::Field;
use ragu_core::{Result, drivers::Driver, gadgets::Bound};

use alloc::boxed::Box;

use crate::io::{Buffer, Write};

impl<F: Field> Write<F> for () {
    fn len() -> usize {
        0
    }

    fn write_gadget<'dr, D: Driver<'dr, F = F>>(_: &(), _: &mut impl Buffer<'dr, D>) -> Result<()> {
        Ok(())
    }
}

impl<F: Field, G: Write<F>, const N: usize> Write<F> for [::core::marker::PhantomData<G>; N] {
    fn len() -> usize {
        N * G::len()
    }

    fn write_gadget<'dr, D: Driver<'dr, F = F>>(
        this: &[Bound<'dr, D, G>; N],
        buf: &mut impl Buffer<'dr, D>,
    ) -> Result<()> {
        for item in this {
            G::write_gadget(item, buf)?;
        }
        Ok(())
    }
}

impl<F: Field, G1: Write<F>, G2: Write<F>> Write<F>
    for (
        ::core::marker::PhantomData<G1>,
        ::core::marker::PhantomData<G2>,
    )
{
    fn len() -> usize {
        G1::len() + G2::len()
    }

    fn write_gadget<'dr, D: Driver<'dr, F = F>>(
        this: &(Bound<'dr, D, G1>, Bound<'dr, D, G2>),
        buf: &mut impl Buffer<'dr, D>,
    ) -> Result<()> {
        G1::write_gadget(&this.0, buf)?;
        G2::write_gadget(&this.1, buf)?;
        Ok(())
    }
}

impl<F: Field, G: Write<F>> Write<F> for ::core::marker::PhantomData<Box<G>> {
    fn len() -> usize {
        G::len()
    }

    fn write_gadget<'dr, D: Driver<'dr, F = F>>(
        this: &Box<Bound<'dr, D, G>>,
        buf: &mut impl Buffer<'dr, D>,
    ) -> Result<()> {
        G::write_gadget(this, buf)
    }
}
