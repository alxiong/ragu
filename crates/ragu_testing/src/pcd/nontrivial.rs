//! Nontrivial test fixtures with Poseidon hashing.

use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
};
use ragu_pcd::{header::Header, step::Step};
use ragu_primitives::{Element, poseidon::Sponge};

pub struct LeafNode;

impl<F: Field> Header<F> for LeafNode {
    type Data = F;
    type Output = Kind![F; Element<'_, _>];

    fn encode<'dr, D: Driver<'dr, F = F>>(
        dr: &mut D,
        witness: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, witness)
    }
}

pub struct InternalNode;

impl<F: Field> Header<F> for InternalNode {
    type Data = F;
    type Output = Kind![F; Element<'_, _>];

    fn encode<'dr, D: Driver<'dr, F = F>>(
        dr: &mut D,
        witness: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, witness)
    }
}

pub struct Hash2<'params, C: Cycle> {
    pub poseidon_params: &'params C::CircuitPoseidon,
}

impl<C: Cycle> Step<C> for Hash2<'_, C> {
    type Witness = ();
    type Aux = ();
    type Left = LeafNode;
    type Right = LeafNode;
    type Output = InternalNode;

    fn synthesize<'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness>,
        left: &Bound<'dr, D, <Self::Left as Header<C::CircuitField>>::Output>,
        right: &Bound<'dr, D, <Self::Right as Header<C::CircuitField>>::Output>,
    ) -> Result<(
        Bound<'dr, D, <Self::Output as Header<C::CircuitField>>::Output>,
        DriverValue<D, <Self::Output as Header<C::CircuitField>>::Data>,
        DriverValue<D, Self::Aux>,
    )>
    where
        Self: 'dr,
    {
        let mut sponge = Sponge::new(dr, self.poseidon_params);
        sponge.absorb(dr, left)?;
        sponge.absorb(dr, right)?;
        let output = sponge.squeeze(dr)?;
        let output_data = output.value().map(|v| *v);

        Ok((output, output_data, D::unit()))
    }
}

pub struct WitnessLeaf<'params, C: Cycle> {
    pub poseidon_params: &'params C::CircuitPoseidon,
}

impl<C: Cycle> Step<C> for WitnessLeaf<'_, C> {
    type Witness = C::CircuitField;
    type Aux = ();
    type Left = ();
    type Right = ();
    type Output = LeafNode;

    fn synthesize<'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness>,
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
        let leaf = Element::alloc(dr, witness)?;
        let mut sponge = Sponge::new(dr, self.poseidon_params);
        sponge.absorb(dr, &leaf)?;
        let leaf = sponge.squeeze(dr)?;
        let leaf_data = leaf.value().map(|v| *v);

        Ok((leaf, leaf_data, D::unit()))
    }
}
