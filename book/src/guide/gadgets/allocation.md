# Allocation

Drivers allocate four wires at a time via [`gate()`]. Circuit code
frequently needs standalone wires, a single field element, a boolean
flag, a hash input. The [`Allocator`] trait bridges this gap, living
in `ragu_primitives` as a separate concern from the core driver.

## The Gate's Slack Wires {#slack-wires}

Recall from the [driver types](../drivers/index.md#drivertypes)
discussion that [`gate()`] produces three wires $(A, B, C)$ and an
`Extra` token representing $D$, subject to $A \cdot B = C$ and
$C \cdot D = 0$. When $A = C = 0$, both
constraints are trivially satisfied: any value of $B$ is compatible
with $0 \cdot B = 0$, and the auxiliary constraint $0 \cdot D = 0$
holds for any $D$. A single gate therefore contains **two
unconstrained slots** — $B$ and $D$ — that an allocator can hand out
independently.

## The [`Allocator`] Trait {#allocator-trait}

```rust,ignore
pub trait Allocator<'dr, D: Driver<'dr>> {
    fn alloc(
        &mut self,
        dr: &mut D,
        value: impl Fn() -> Result<Coeff<D::F>>,
    ) -> Result<D::Wire>;
}
```

[`Element::alloc`] takes an `&mut A` parameter where
`A: Allocator`, so the caller chooses the allocation strategy:

```rust,ignore
let x = Element::alloc(dr, &mut allocator, witness)?;
```

The `value` closure in `Allocator::alloc` follows the same purity
contract as [`Driver::mul`]: it may be called zero or more times
and must be side-effect-free.

## The Unit Allocator {#unit-allocator}

The simplest allocator is `()`. Each call invokes [`mul()`] with
$A = C = 0$ and returns the $B$ wire. Because `mul()` delegates to
`gate()` and discards the `Extra` token internally, the $D$ slot
goes unused:

```rust,ignore
impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for () {
    fn alloc(
        &mut self,
        dr: &mut D,
        value: impl Fn() -> Result<Coeff<D::F>>,
    ) -> Result<D::Wire> {
        let (_, b, _) = dr.mul(
            || Ok((Coeff::Zero, value()?, Coeff::Zero)),
        )?;
        Ok(b)
    }
}
```

Call site:

```rust,ignore
let x = Element::alloc(dr, &mut (), witness)?;
```

One gate per wire — stateless, but wasteful when allocations come in
pairs.

## [`SimpleAllocator`] {#simple-allocator}

[`SimpleAllocator`] pairs consecutive allocations into a single gate,
halving the gate cost:

1. **First call:** allocates a gate with $A = C = 0$, returns $B$,
   and stashes the `Extra` token for $D$.
2. **Second call:** redeems the stashed token via
   [`assign_extra`][assign-extra], returning $D$ without allocating a
   new gate.

```rust,ignore
impl<'dr, D: Driver<'dr>> Allocator<'dr, D>
    for SimpleAllocator<D::Extra>
{
    fn alloc(
        &mut self,
        dr: &mut D,
        value: impl Fn() -> Result<Coeff<D::F>>,
    ) -> Result<D::Wire> {
        if let Some(extra) = self.stash.take() {
            dr.assign_extra(extra, value)
        } else {
            let (_, b, _, extra) = dr.gate(
                || Ok((Coeff::Zero, value()?, Coeff::Zero)),
            )?;
            self.stash = Some(extra);
            Ok(b)
        }
    }
}
```

Typical usage:

```rust,ignore
let allocator = &mut SimpleAllocator::new();
let a = Element::alloc(dr, allocator, witness_a)?;
let b = Element::alloc(dr, allocator, witness_b)?;
// Both a and b share one gate.
```

```admonish info
Dropping a `SimpleAllocator` that still holds a stashed token is
safe. The driver already assigned $D = 0$ for that gate, so no
constraint is violated.
```

## Choosing an Allocator {#choosing}

| Situation | Allocator |
|-----------|-----------|
| Two or more consecutive allocations | [`SimpleAllocator`] |
| Single isolated allocation | `()` |

[`SimpleAllocator`] is the right default whenever you allocate more
than one wire in sequence. Use `()` when a single allocation is truly
standalone and introducing a `SimpleAllocator` would add unnecessary
state.

```admonish tip
[`Boolean::alloc`] bypasses `Allocator` entirely, it uses
[`mul()`] directly to constrain $a \cdot (1 - a) = 0$, costing one
gate and two linear constraints. You do not need an allocator for
booleans.
```

## Cost Accounting {#cost-accounting}

The [Simulator](../drivers/simulator.md) makes allocation costs
visible. Compare two unit allocations against one paired allocation:

```rust,ignore
// Two unit allocations: 2 gates
let sim = Simulator::simulate((a, b), |dr, witness| {
    let (a, b) = witness.cast();
    let _ = Element::alloc(dr, &mut (), a)?;
    let _ = Element::alloc(dr, &mut (), b)?;
    Ok(())
})?;
assert_eq!(sim.num_gates(), 2);

// Two paired allocations: 1 gate
let sim = Simulator::simulate((a, b), |dr, witness| {
    let (a, b) = witness.cast();
    let alloc = &mut SimpleAllocator::new();
    let _ = Element::alloc(dr, alloc, a)?;
    let _ = Element::alloc(dr, alloc, b)?;
    Ok(())
})?;
assert_eq!(sim.num_gates(), 1);
```

The next section introduces the
[`GadgetKind` trait](gadgetkind.md), which defines how gadget types
interact with conversion and wire mapping.

[`gate()`]: ragu_core::drivers::DriverTypes::gate
[`Allocator`]: ragu_primitives::allocator::Allocator
[`Element::alloc`]: ragu_primitives::Element::alloc
[`Driver::mul`]: ragu_core::drivers::Driver::mul
[`SimpleAllocator`]: ragu_primitives::allocator::SimpleAllocator
[assign-extra]: ragu_core::drivers::DriverTypes::assign_extra
[`Boolean::alloc`]: ragu_primitives::Boolean::alloc
[`mul()`]: ragu_core::drivers::Driver::mul
