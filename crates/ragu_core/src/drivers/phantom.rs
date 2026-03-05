use super::{Coeff, Driver, DriverTypes, Field, Result};

/// This is a dummy driver that does absolutely nothing.
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
