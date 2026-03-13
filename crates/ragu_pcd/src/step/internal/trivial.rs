//! Internal step that produces a valid proof with trivial header.
//!
//! Used in rerandomization to create a properly-structured trivial proof that
//! can be folded with a valid proof without causing C value mismatches.

use ragu_arithmetic::Cycle;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Bound,
};

use super::super::Step;
use crate::Header;

pub(crate) struct Trivial;

impl Trivial {
    pub fn new() -> Self {
        Trivial
    }
}

impl<C: Cycle> Step<C> for Trivial {
    type Witness = ();
    type Aux = ();

    type Left = ();
    type Right = ();
    type Output = ();

    fn synthesize<'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        _dr: &mut D,
        _: DriverValue<D, Self::Witness>,
        _left: &Bound<'dr, D, <Self::Left as Header<C::CircuitField>>::Output>,
        _right: &Bound<'dr, D, <Self::Right as Header<C::CircuitField>>::Output>,
    ) -> Result<(
        Bound<'dr, D, <Self::Output as Header<C::CircuitField>>::Output>,
        DriverValue<D, <Self::Output as Header<C::CircuitField>>::Data>,
        DriverValue<D, Self::Aux>,
    )>
    where
        Self: 'dr,
    {
        Ok(((), D::unit(), D::unit()))
    }
}
