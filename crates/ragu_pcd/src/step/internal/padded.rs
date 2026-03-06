use ff::{Field, PrimeField};
use ragu_core::{
    Result,
    drivers::Driver,
    gadgets::{Bound, Gadget, GadgetKind, Kind},
};
use ragu_primitives::{
    Element,
    io::{Counter, Write},
    vec::{FixedVec, Len},
};

use core::marker::PhantomData;

use crate::Header;
use crate::components::suffix::WithSuffix;

/// A header gadget padded to a fixed size with a suffix element appended.
///
/// The serialization order is `[gadget_data | zeros | suffix]`:
/// - First, the header gadget data
/// - Then, zero padding to fill up to `HEADER_SIZE - 1` elements
/// - Finally, the suffix element at position `HEADER_SIZE - 1`
#[derive(Gadget, Write)]
pub(crate) struct Padded<
    'dr,
    D: Driver<'dr>,
    G: GadgetKind<D::F> + Write<D::F>,
    const HEADER_SIZE: usize,
> {
    #[ragu(gadget)]
    inner: WithSuffix<'dr, D, Kind![D::F; PaddedContent<'_, _, G, HEADER_SIZE>]>,
}

/// Constructs a [`Padded`] gadget representing a gadget for a [`Header`] padded
/// to some fixed size `HEADER_SIZE` encoding, including the header suffix.
pub(crate) fn for_header<
    'dr,
    H: Header<D::F>,
    const HEADER_SIZE: usize,
    D: Driver<'dr, F: PrimeField>,
>(
    dr: &mut D,
    gadget: Bound<'dr, D, H::Output>,
) -> Result<Padded<'dr, D, H::Output, HEADER_SIZE>> {
    // Count the elements the gadget writes, and validate against HEADER_SIZE.
    let mut count = Counter::default();
    H::Output::write_gadget(&gadget, &mut count)?;
    let count = count.value();

    let pad_count = (HEADER_SIZE - 1).checked_sub(count).ok_or_else(|| {
        ragu_core::Error::MalformedEncoding(
            alloc::format!(
                "Header encoding size exceeded HEADER_SIZE - 1 ({})",
                HEADER_SIZE - 1,
            )
            .into(),
        )
    })?;

    let padding = FixedVec::new((0..pad_count).map(|_| Element::zero(dr)).collect())?;
    let suffix = Element::constant(dr, D::F::from(H::SUFFIX.get()));

    Ok(Padded {
        inner: WithSuffix::new(PaddedContent { gadget, padding }, suffix),
    })
}

/// Encodes the zero-padding length as a [`Len`] type so that [`PaddedContent`]
/// can use [`FixedVec`] rather than a dynamic `Vec`.
///
/// `len() = HEADER_SIZE - 1 - G::len()`
struct PadLen<const HEADER_SIZE: usize, F: Field, G: Write<F>>(
    // a compiler trick to satisfy the `G: Sync` hint for `trait Len: Sync`
    PhantomData<fn() -> (F, G)>,
);

impl<const HEADER_SIZE: usize, F: Field, G: Write<F>> Len for PadLen<HEADER_SIZE, F, G> {
    fn len() -> usize {
        HEADER_SIZE - 1 - G::len()
    }
}

/// Inner gadget that writes the header gadget followed by pre-allocated zero
/// padding up to `HEADER_SIZE - 1` elements (reserving space for the suffix).
#[derive(Gadget, Write)]
pub(crate) struct PaddedContent<
    'dr,
    D: Driver<'dr>,
    G: GadgetKind<D::F> + Write<D::F>,
    const HEADER_SIZE: usize,
> {
    #[ragu(gadget)]
    gadget: Bound<'dr, D, G>,
    #[ragu(gadget)]
    padding: FixedVec<Element<'dr, D>, PadLen<HEADER_SIZE, D::F, G>>,
}

#[cfg(test)]
mod tests {
    use ragu_core::{
        Result,
        drivers::{Driver, DriverValue, emulator::Emulator},
        gadgets::{Bound, Gadget, Kind},
        maybe::{Always, Maybe, MaybeKind},
    };
    use ragu_pasta::Fp as F;
    use ragu_primitives::{
        Element, GadgetExt,
        io::Write,
        vec::{CollectFixed, ConstLen, FixedVec},
    };

    use super::{PadLen, Padded};
    use crate::{Header, components::suffix::WithSuffix, header::Suffix};

    #[derive(Gadget, Write)]
    struct MySillyGadget<'dr, D: Driver<'dr>> {
        #[ragu(gadget)]
        blah: FixedVec<Element<'dr, D>, ConstLen<4>>,
    }

    // A header whose Output is MySillyGadget (4 elements).
    struct MySillyHeader;
    impl Header<F> for MySillyHeader {
        const SUFFIX: Suffix = Suffix::new(0);
        type Data<'source> = ();
        type Output = Kind![F; MySillyGadget<'_, _>];

        fn encode<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
            dr: &mut D,
            _: DriverValue<D, ()>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            let blah = (1u64..=4)
                .map(|n| Element::alloc(dr, D::just(|| F::from(n))))
                .try_collect_fixed()?;
            Ok(MySillyGadget { blah })
        }
    }

    #[test]
    fn test_write() -> Result<()> {
        let mut dr = Emulator::execute();
        let dr = &mut dr;
        let gadget = MySillyGadget {
            blah: (1u64..=4)
                .map(|n| Element::alloc(dr, Always::maybe_just(|| F::from(n))))
                .try_collect_fixed()?,
        };

        {
            // Create Padded gadget with suffix value 42 and 1 zero padding
            // HEADER_SIZE=6: 4 gadget elements + 1 zero + 1 suffix
            let padding = FixedVec::<_, PadLen<6, F, Kind![F; MySillyGadget<'_, _>]>>::new(vec![
                Element::zero(dr),
            ])?;
            let padded_content = super::PaddedContent::<'_, _, Kind![F; MySillyGadget<'_, _>], 6> {
                gadget: gadget.clone(),
                padding,
            };
            let padded_gadget = Padded::<'_, _, Kind![F; MySillyGadget<'_, _>], 6> {
                inner: WithSuffix::new(padded_content, Element::constant(dr, F::from(42u64))),
            };
            let mut buffer = vec![];
            padded_gadget.write(&mut buffer)?;

            // Expected: [1, 2, 3, 4, 0, 42] - gadget data, zero padding, suffix
            assert_eq!(buffer.len(), 6);
            assert_eq!(*buffer[0].value().take(), F::from(1u64));
            assert_eq!(*buffer[1].value().take(), F::from(2u64));
            assert_eq!(*buffer[2].value().take(), F::from(3u64));
            assert_eq!(*buffer[3].value().take(), F::from(4u64));
            assert_eq!(*buffer[4].value().take(), F::from(0u64));
            assert_eq!(*buffer[5].value().take(), F::from(42u64)); // suffix at end
        }

        Ok(())
    }

    #[test]
    fn test_exceeding_buffer() -> Result<()> {
        let mut dr = Emulator::execute();
        let dr = &mut dr;
        let gadget = MySillyGadget {
            blah: (1u64..=4)
                .map(|n| Element::alloc(dr, Always::maybe_just(|| F::from(n))))
                .try_collect_fixed()?,
        };

        // HEADER_SIZE=4 means only 3 elements for content (4 - 1 for suffix).
        // MySillyHeader has 4 elements, so for_header should fail.
        assert!(
            super::for_header::<MySillyHeader, 4, _>(dr, gadget).is_err(),
            "for_header should fail when gadget exceeds HEADER_SIZE - 1"
        );

        Ok(())
    }
}
