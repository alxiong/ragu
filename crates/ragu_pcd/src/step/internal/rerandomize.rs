//! Rerandomization circuit.
//!
//! A dedicated circuit for rerandomization, using uniform encoding for the
//! left input header to ensure circuit uniformity across header types.
//!
//! Unlike [`Adapter`](super::adapter::Adapter), this does not wrap a [`Step`](crate::step::Step)
//! — rerandomization has no synthesis logic. The circuit simply encodes the left
//! header uniformly, encodes a trivial right header, and copies the left as the
//! output.

use ragu_arithmetic::Cycle;
use ragu_circuits::{Circuit, polynomials::Rank};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
};
use ragu_primitives::{
    Element,
    vec::{CollectFixed, ConstLen, FixedVec},
};

use alloc::vec::Vec;
use core::marker::PhantomData;

use super::adapter::TripleConstLen;
use crate::Header;
use crate::header::Suffix;
use crate::step::Encoded;

/// Rerandomization circuit.
///
/// Uses uniform encoding for the left input header to ensure circuit uniformity
/// across header types. Registered with `H = ()` for circuit shape, but used at
/// runtime with the actual header type `H`.
pub(crate) struct Rerandomize<C, H, R, const HEADER_SIZE: usize> {
    left_suffix: Suffix,
    right_suffix: Suffix,
    _marker: PhantomData<(C, H, R)>,
}

impl<C: Cycle, H: Header<C::CircuitField>, R: Rank, const HEADER_SIZE: usize>
    Rerandomize<C, H, R, HEADER_SIZE>
{
    pub fn new(left_suffix: Suffix, right_suffix: Suffix) -> Self {
        Self {
            left_suffix,
            right_suffix,
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, H: Header<C::CircuitField>, R: Rank, const HEADER_SIZE: usize>
    Circuit<C::CircuitField> for Rerandomize<C, H, R, HEADER_SIZE>
{
    type Instance = ();
    type Witness = H::Data;
    type Output = Kind![C::CircuitField; FixedVec<Element<'_, _>, TripleConstLen<HEADER_SIZE>>];
    type Aux = (
        FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
        FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
    );

    fn instance<'dr, D: Driver<'dr, F = C::CircuitField>>(
        &self,
        _: &mut D,
        _: DriverValue<D, Self::Instance>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        unreachable!("k(Y) is computed manually for ragu_pcd circuit implementations")
    }

    fn witness<'dr, D: Driver<'dr, F = C::CircuitField>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness>,
    ) -> Result<(Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux>)>
    where
        Self: 'dr,
    {
        // Uniform encoding for left ensures circuit uniformity across header types
        let left_enc = Encoded::<_, H, HEADER_SIZE>::new_uniform(dr, witness, self.left_suffix)?;
        // Standard encoding for right (trivial header)
        let right_enc = Encoded::<_, (), HEADER_SIZE>::new(dr, D::unit(), self.right_suffix)?;

        let mut elements = Vec::with_capacity(HEADER_SIZE * 3);
        left_enc.clone().write(dr, &mut elements)?;
        right_enc.write(dr, &mut elements)?;
        left_enc.write(dr, &mut elements)?; // output = left

        let adapter_aux = D::try_just(|| {
            let left_header = elements[0..HEADER_SIZE]
                .iter()
                .map(|e| *e.value().take())
                .collect_fixed()?;
            let right_header = elements[HEADER_SIZE..HEADER_SIZE * 2]
                .iter()
                .map(|e| *e.value().take())
                .collect_fixed()?;
            Ok((left_header, right_header))
        })?;

        Ok((FixedVec::try_from(elements)?, adapter_aux))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::header::Header;
    use ragu_circuits::{CircuitExt, polynomials, registry};
    use ragu_core::{
        drivers::{Driver, DriverValue},
        gadgets::{Bound, Kind},
    };
    use ragu_pasta::{Fp, Pasta};

    type TestR = polynomials::TestRank;
    const HEADER_SIZE: usize = 4;

    struct TestHeader;

    impl Header<Fp> for TestHeader {
        type Data = Fp;
        type Output = Kind![Fp; Element<'_, _>];

        fn encode<'dr, D: Driver<'dr, F = Fp>>(
            dr: &mut D,
            witness: DriverValue<D, Self::Data>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            Element::alloc(dr, witness)
        }
    }

    struct PairHeader;
    impl Header<Fp> for PairHeader {
        type Data = (Fp, Fp);
        type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
        fn encode<'dr, D: Driver<'dr, F = Fp>>(
            dr: &mut D,
            witness: DriverValue<D, Self::Data>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            let (a, b) = witness.cast();
            Ok((Element::alloc(dr, a)?, Element::alloc(dr, b)?))
        }
    }

    #[test]
    fn uniform_across_header_types() {
        let circuit_single = Rerandomize::<Pasta, TestHeader, TestR, HEADER_SIZE>::new(
            Suffix::new(0),
            Suffix::internal(1),
        )
        .into_object::<TestR>()
        .unwrap();
        let circuit_pair = Rerandomize::<Pasta, PairHeader, TestR, HEADER_SIZE>::new(
            Suffix::new(1),
            Suffix::internal(1),
        )
        .into_object::<TestR>()
        .unwrap();

        let x = Fp::from(5u64);
        let y = Fp::from(17u64);
        let key = registry::Key::default();

        let floor_plan_single =
            ragu_circuits::floor_planner::floor_plan(circuit_single.segment_records());
        let floor_plan_pair =
            ragu_circuits::floor_planner::floor_plan(circuit_pair.segment_records());

        let eval_single = circuit_single.sxy(x, y, &key, &floor_plan_single);
        let eval_pair = circuit_pair.sxy(x, y, &key, &floor_plan_pair);

        assert_eq!(eval_single, eval_pair);
    }
}
