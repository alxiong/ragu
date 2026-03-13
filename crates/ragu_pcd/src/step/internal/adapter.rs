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
    vec::{CollectFixed, ConstLen, FixedVec, Len},
};

use alloc::vec::Vec;
use core::marker::PhantomData;

use super::super::Step;
use crate::Header;
use crate::header::Suffix;
use crate::step::Encoded;

/// Represents triple a length determined at compile time.
pub struct TripleConstLen<const N: usize>;

impl<const N: usize> Len for TripleConstLen<N> {
    fn len() -> usize {
        N * 3
    }
}

/// Internal wrapper that bundles left/right/output header suffixes to a Step.
/// Our runtime suffix assignment necessitates an exdogenous passing of suffixes
/// to the circuit Adapter for a step.
pub(crate) struct StepWithSuffixes<S> {
    pub(crate) step: S,
    pub(crate) left_suffix: Suffix,
    pub(crate) right_suffix: Suffix,
    pub(crate) output_suffix: Suffix,
}

pub(crate) struct Adapter<C, S, R, const HEADER_SIZE: usize> {
    inner: StepWithSuffixes<S>,
    _marker: PhantomData<(C, R)>,
}

impl<C: Cycle, S: Step<C>, R: Rank, const HEADER_SIZE: usize> Adapter<C, S, R, HEADER_SIZE> {
    pub fn new(inner: StepWithSuffixes<S>) -> Self {
        Adapter {
            inner,
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, S: Step<C>, R: Rank, const HEADER_SIZE: usize> Circuit<C::CircuitField>
    for Adapter<C, S, R, HEADER_SIZE>
{
    type Instance = (
        FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
        FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
        <S::Output as Header<C::CircuitField>>::Data,
    );
    type Witness = (
        <S::Left as Header<C::CircuitField>>::Data,
        <S::Right as Header<C::CircuitField>>::Data,
        S::Witness,
    );
    type Output = Kind![C::CircuitField; FixedVec<Element<'_, _>, TripleConstLen<HEADER_SIZE>>];
    type Aux = (
        (
            FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
            FixedVec<C::CircuitField, ConstLen<HEADER_SIZE>>,
        ),
        <S::Output as Header<C::CircuitField>>::Data,
        S::Aux,
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
        let (left_data, right_data, step_witness) = witness.cast();
        let s = &self.inner;

        let left_enc = Encoded::<_, S::Left, HEADER_SIZE>::new(dr, left_data, s.left_suffix)?;
        let right_enc = Encoded::<_, S::Right, HEADER_SIZE>::new(dr, right_data, s.right_suffix)?;

        let (output_gadget, output_data, step_aux) = s.step.synthesize::<D, HEADER_SIZE>(
            dr,
            step_witness,
            left_enc.as_gadget(),
            right_enc.as_gadget(),
        )?;
        let output_enc =
            Encoded::<_, S::Output, HEADER_SIZE>::from_gadget(output_gadget, s.output_suffix);

        let mut elements = Vec::with_capacity(HEADER_SIZE * 3);
        left_enc.write(dr, &mut elements)?;
        right_enc.write(dr, &mut elements)?;
        output_enc.write(dr, &mut elements)?;

        let adapter_aux = D::try_just(|| {
            let left_header = elements[0..HEADER_SIZE]
                .iter()
                .map(|e| *e.value().take())
                .collect_fixed()?;
            let right_header = elements[HEADER_SIZE..HEADER_SIZE * 2]
                .iter()
                .map(|e| *e.value().take())
                .collect_fixed()?;
            Ok((
                (left_header, right_header),
                output_data.take(),
                step_aux.take(),
            ))
        })?;

        Ok((FixedVec::try_from(elements)?, adapter_aux))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::header::Header;
    use crate::step::Step;
    use ragu_circuits::polynomials::TestRank;
    use ragu_core::{
        drivers::emulator::Emulator,
        gadgets::{Bound, Kind},
        maybe::{Always, Maybe, MaybeKind},
    };
    use ragu_pasta::{Fp, Pasta};

    type TestR = TestRank;
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

    struct TestStep;

    impl Step<Pasta> for TestStep {
        type Witness = ();
        type Aux = ();
        type Left = TestHeader;
        type Right = TestHeader;
        type Output = TestHeader;

        fn synthesize<'dr, D: Driver<'dr, F = Fp>, const HS: usize>(
            &self,
            dr: &mut D,
            _: DriverValue<D, ()>,
            left: &Bound<'dr, D, <TestHeader as Header<Fp>>::Output>,
            right: &Bound<'dr, D, <TestHeader as Header<Fp>>::Output>,
        ) -> Result<(
            Bound<'dr, D, <TestHeader as Header<Fp>>::Output>,
            DriverValue<D, Fp>,
            DriverValue<D, ()>,
        )>
        where
            Self: 'dr,
        {
            // Output is sum of left and right
            let output_elem = left.add(dr, right);
            let output_val = output_elem.value().map(|v| *v);
            Ok((output_elem, output_val, D::unit()))
        }
    }

    #[test]
    fn triple_const_len_returns_3n() {
        assert_eq!(TripleConstLen::<1>::len(), 3);
        assert_eq!(TripleConstLen::<4>::len(), 12);
        assert_eq!(TripleConstLen::<10>::len(), 30);
    }

    #[test]
    fn adapter_witness_produces_correct_output_size() {
        let mut dr = Emulator::execute();
        let dr = &mut dr;

        let adapter = Adapter::<Pasta, TestStep, TestR, HEADER_SIZE>::new(StepWithSuffixes {
            step: TestStep,
            left_suffix: Suffix::new(50),
            right_suffix: Suffix::new(50),
            output_suffix: Suffix::new(50),
        });
        let witness = Always::maybe_just(|| (Fp::from(10u64), Fp::from(20u64), ()));

        let (output, _aux) = adapter
            .witness(dr, witness)
            .expect("witness should succeed");

        // Output should have 3 * HEADER_SIZE elements (left + right + output headers)
        assert_eq!(output.len(), HEADER_SIZE * 3);
    }

    #[test]
    fn adapter_witness_extracts_aux_correctly() {
        let mut dr = Emulator::execute();
        let dr = &mut dr;

        let adapter = Adapter::<Pasta, TestStep, TestR, HEADER_SIZE>::new(StepWithSuffixes {
            step: TestStep,
            left_suffix: Suffix::new(50),
            right_suffix: Suffix::new(50),
            output_suffix: Suffix::new(50),
        });
        let witness = Always::maybe_just(|| (Fp::from(10u64), Fp::from(20u64), ()));

        let (_output, aux) = adapter
            .witness(dr, witness)
            .expect("witness should succeed");

        let ((left_header, right_header), output_data, _step_aux) = aux.take();

        // Left header should start with 10
        assert_eq!(left_header[0], Fp::from(10u64));
        // Right header should start with 20
        assert_eq!(right_header[0], Fp::from(20u64));
        // Step aux should be 10 + 20 = 30
        assert_eq!(output_data, Fp::from(30u64));
    }
}
