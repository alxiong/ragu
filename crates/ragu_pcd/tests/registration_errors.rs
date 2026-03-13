use ff::Field;
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Bound,
};
use ragu_pasta::Pasta;
use ragu_pcd::{ApplicationBuilder, header::Header, step::Step};

// Header A
struct HSuffixA;

impl<F: Field> Header<F> for HSuffixA {
    type Data = ();
    type Output = ();
    fn encode<'dr, D: Driver<'dr, F = F>>(
        _: &mut D,
        _: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Ok(())
    }
}

// Header B
struct HSuffixB;

impl<F: Field> Header<F> for HSuffixB {
    type Data = ();
    type Output = ();
    fn encode<'dr, D: Driver<'dr, F = F>>(
        _: &mut D,
        _: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Ok(())
    }
}

// Step 0 -> produces HSuffixA
struct Step0;
impl<C: ragu_arithmetic::Cycle> Step<C> for Step0 {
    type Witness = ();
    type Aux = ();
    type Left = ();
    type Right = ();
    type Output = HSuffixA;
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

// Step 1 -> consumes A and produces B
struct Step1;
impl<C: ragu_arithmetic::Cycle> Step<C> for Step1 {
    type Witness = ();
    type Aux = ();
    type Left = HSuffixA;
    type Right = HSuffixA;
    type Output = HSuffixB;
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

#[test]
fn register_steps_success_and_finalize() {
    let pasta = Pasta::baked();
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step1)
        .unwrap()
        .finalize(pasta)
        .unwrap();
}

#[test]
fn auto_suffix_assignment_different_types_get_different_suffixes() {
    // With auto-assigned suffixes, different Header types automatically get
    // different suffixes. This test verifies that registration with multiple
    // header types succeeds.
    let pasta = Pasta::baked();
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step1)
        .unwrap()
        .finalize(pasta)
        .unwrap();
}

#[test]
fn duplicate_step_type_registration_errors() {
    let result = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step0);
    assert!(
        result.is_err(),
        "registering the same step type twice should error"
    );
}
