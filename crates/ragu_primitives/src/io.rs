//! Traits for serializing gadgets into buffers.
//!
//! The [`Write`] trait allows compatible [`Gadget`](crate::Gadget)s
//! to write [`Element`]s to a [`Buffer`] for serialization purposes. Because
//! gadgets are just containers for wires and witness data, they can usually
//! reconstitute their encapsulated [`Element`]s via promotion.
//!
//! The [`Sink`] trait allows destination sinks to receive a [`Driver`] for
//! processing the elements they receive. This is handy for streaming hash
//! functions. Specific gadgets can have more optimal serialization strategies
//! by leveraging the provided [`Driver`] as well: as an example, a gadget that
//! contains multiple [`Boolean`](crate::Boolean)s can
//! [pack](crate::boolean::multipack) many of them into far fewer [`Element`]s.

mod pipe;

use ff::Field;
use ragu_core::{
    Result,
    drivers::Driver,
    gadgets::{Bound, GadgetKind},
};

use crate::Element;

pub use pipe::Pipe;

/// A plain destination for [`Element`]s that does not cause any side effects
/// on the driver context when being written.
pub trait Buffer<'dr, D: Driver<'dr>> {
    /// Push a single [`Element`] into this buffer.
    fn write(&mut self, value: &Element<'dr, D>) -> Result<()>;
}

/// Represents a gadget that can be serialized into a sequence of [`Element`]s
/// that are written to a [`Buffer`].
///
/// Gadget serialization is implemented as a subtrait of [`GadgetKind`] to
/// satisfy Rust language restrictions and keep interfaces ergonomic. Concrete
/// [`Gadget`](crate::Gadget)s can be serialized using the
/// [`GadgetExt::write`](crate::GadgetExt::write) helper method.
///
/// ### Automatic Derivation
///
/// Gadgets that consist mainly of other gadgets are candidates for [automatic
/// derivation](derive@Write) of this trait.
pub trait Write<F: Field>: GadgetKind<F> {
    /// Write this gadget's elements into the provided buffer.
    fn write_gadget<'dr, D: Driver<'dr, F = F>>(
        this: &Bound<'dr, D, Self>,
        buf: &mut impl Buffer<'dr, D>,
    ) -> Result<()>;
}

/// Represents a general destination for [`Element`]s to be written to and
/// processed using a provided [`Driver`] context. This may cause side effects
/// on the driver in contrast to a [`Buffer`], which is a passive destination
/// for elements.
pub trait Sink<'dr, D: Driver<'dr>> {
    /// Push an `Element` into this sink using the provided driver `D`.
    fn write(&mut self, dr: &mut D, value: &Element<'dr, D>) -> Result<()>;
}

/// Automatically derives the [`Write`] trait for gadgets that merely
/// contain other gadgets.
///
/// This only works for structs with named fields. Similar to the
/// [`Gadget`](derive@ragu_core::gadgets::Gadget) derive macro, the driver type
/// can be annotated with `#[ragu(driver)]`. Fields with `#[ragu(skip)]` or
/// `#[ragu(phantom)]` annotations are ignored.
///
/// ## Example
///
/// ```rust
/// # use ragu_arithmetic::CurveAffine;
/// # use ragu_core::{drivers::{Driver, DriverValue}, gadgets::Gadget};
/// # use ragu_primitives::{Element, io::Write};
/// # use core::marker::PhantomData;
/// #[derive(Gadget, Write)]
/// pub struct Point<'dr, D: Driver<'dr>, C: CurveAffine> {
///     #[ragu(gadget)]
///     x: Element<'dr, D>,
///     #[ragu(gadget)]
///     y: Element<'dr, D>,
///     #[ragu(phantom)]
///     _marker: PhantomData<C>,
/// }
/// ```
pub use ragu_macros::Write;

/// A [`Buffer`] that counts the number of [`Element`]s written, discarding their values.
#[derive(Default)]
pub struct Counter(usize);

impl Counter {
    /// Returns the number of elements written so far.
    pub fn value(&self) -> usize {
        self.0
    }
}

impl<'dr, D: Driver<'dr>> Buffer<'dr, D> for Counter {
    fn write(&mut self, _: &Element<'dr, D>) -> Result<()> {
        self.0 += 1;
        Ok(())
    }
}
