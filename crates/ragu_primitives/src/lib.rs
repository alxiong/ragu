//! # `ragu_primitives`
//!
//! This crate contains low level gadgets and algorithms for the Ragu project.
//! This API is re-exported (as necessary) in other crates and so this crate is
//! only intended to be used internally by Ragu.

#![no_std]
#![allow(clippy::type_complexity)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![doc(html_favicon_url = "https://tachyon.z.cash/assets/ragu/v1/favicon-32x32.png")]
#![doc(html_logo_url = "https://tachyon.z.cash/assets/ragu/v1/rustdoc-128x128.png")]

extern crate alloc;
extern crate self as ragu_primitives;

mod boolean;
mod element;
mod endoscalar;
mod foreign;
pub mod io;
mod point;
pub mod poseidon;
pub mod promotion;
mod sendable;
mod simulator;
mod util;
pub mod vec;

use ragu_core::{Result, drivers::Driver, gadgets::Gadget};

use core::marker::PhantomData;

use io::{Sink, Write};
use promotion::Demoted;

pub use boolean::{Boolean, multipack};
pub use element::{Element, multiadd};
pub use endoscalar::{Endoscalar, extract_endoscalar, lift_endoscalar};
pub use point::Point;
pub use sendable::Sendable;
pub use simulator::Simulator;

/// Primitive extension trait for all gadgets.
pub trait GadgetExt<'dr, D: Driver<'dr>>: Gadget<'dr, D> {
    /// Write this gadget into a [`Buffer`](io::Buffer), assuming the gadget's
    /// [`Kind`](Gadget::Kind) implements [`Write`].
    fn write(&self, buf: &mut impl io::Buffer<'dr, D>) -> Result<()>
    where
        Self::Kind: Write<D::F>,
    {
        <Self::Kind as Write<D::F>>::write_gadget(self, buf)
    }

    /// Write this gadget into a [`Sink`], assuming the gadget's
    /// [`Kind`](Gadget::Kind) implements [`Write`].
    fn sink<B: Sink<'dr, D>>(&self, dr: &mut D, buf: &mut B) -> Result<()>
    where
        Self::Kind: Write<D::F>,
    {
        // Adapts a Sink into a Buffer by capturing the driver reference,
        // allowing write_gadget (which only receives a Buffer) to forward
        // element writes to a driver-aware Sink.
        struct BufferSink<'a, 'dr, D: Driver<'dr>, B: Sink<'dr, D>> {
            dr: &'a mut D,
            buf: &'a mut B,
            _marker: PhantomData<&'dr ()>,
        }
        impl<'dr, D: Driver<'dr>, B: Sink<'dr, D>> io::Buffer<'dr, D> for BufferSink<'_, 'dr, D, B> {
            fn write(&mut self, value: &Element<'dr, D>) -> Result<()> {
                self.buf.write(self.dr, value)
            }
        }
        self.write(&mut BufferSink {
            dr,
            buf,
            _marker: PhantomData,
        })
    }

    /// Demote this gadget by stripping its witness data.
    fn demote(&self) -> Result<Demoted<'dr, D, Self>> {
        Demoted::new(self)
    }

    /// Wrap this gadget in [`Sendable`], asserting it is [`Send`].
    ///
    /// This is only available when `D::Wire: Send`.
    fn sendable(self) -> Sendable<Self>
    where
        D::Wire: Send,
    {
        Sendable::new::<D>(self)
    }
}

impl<'dr, D: Driver<'dr>, G: Gadget<'dr, D>> GadgetExt<'dr, D> for G {}
