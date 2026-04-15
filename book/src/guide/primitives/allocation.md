# Allocation

All wires are created in groups whenever new gates are created via
[`mul()`] (or, more generally, with [`gate()`]). In some rare cases,
gadgets need _standalone_ wires that cannot be easily represented as
linear combinations of existing wires. The [`Allocator`] trait
generalizes over (possibly stateful) strategies for obtaining free
wires to witness arbitrary data.

## The [`Allocator`] Trait {#allocator-trait}

```rust,ignore
pub trait Allocator<'dr, D: Driver<'dr>> {
    fn alloc(
        &mut self,
        dr: &mut D,
        value: impl Fn() -> Result<Coeff<D::F>>,
    ) -> Result<D::Wire>;

    fn donate(&mut self, _extra: D::Extra) {}
}
```

`Allocator::alloc` takes a mutable reference to the driver and a
witness-producing closure, and returns a single wire. The closure
follows the same purity contract as [`Driver::mul`]: it may be called
zero or more times and must be side-effect-free. Where `Driver::mul`
produces three wires from a multiplication relationship, `alloc`
produces one wire carrying an arbitrary value.

The `donate` method accepts a spare
[`Extra`](ragu_core::drivers::DriverTypes::Extra) token from an
external gate whose $D$ wire is unconstrained. By default it drops
the token; advanced allocators override it to pool spare wires for
reuse.

Gadgets that need standalone wires accept a generic `&mut A` where
`A: Allocator`. For example, [`Element::alloc`] delegates to
whichever allocator the caller provides:

```rust,ignore
let x = Element::alloc(dr, &mut allocator, witness)?;
```

This lets the same gadget code work with any allocation strategy
the caller chooses.

## The Unit Allocator {#unit-allocator}

The simplest allocator is `()`. Each call invokes [`mul()`] with
$A = C = 0$ and returns the $B$ wire:

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

One gate per wire, stateless, but wasteful when allocations come in
pairs.

## [`SimpleAllocator`] {#simple-allocator}

The unit allocator wastes capacity because each gate allocates four
wire slots, but [`gate()`] returns three wires plus a spare `Extra`
token representing the $D$ wire. The gate is subject to
$A \cdot B = C$ and $C \cdot D = 0$. When $A = C = 0$, both
constraints are trivially satisfied and both $B$ and $D$ are
unconstrained. A single gate therefore contains **two free slots**.

[`SimpleAllocator`] exploits this by pairing consecutive allocations
into one gate:

1. **First call:** allocates a gate with $A = C = 0$, returns $B$,
   and stashes the `Extra` token for $D$.
2. **Second call:** redeems the stashed token via
   [`assign_extra`][assign-extra], returning $D$ without allocating
   a new gate.

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

## [`PoolAllocator`] {#pool-allocator}

Some gadgets allocate a gate whose $D$ wire is unconstrained because
$C = 0$. Rather than waste that wire, they can _donate_ the `Extra`
token to the allocator. [`PoolAllocator`] collects these donated
tokens and hands them out on future `alloc` calls before falling
back to new gates.

[`Boolean::alloc`] is the canonical example. The boolean constraint
$a \cdot (1 - a) = 0$ produces a gate where $C = 0$, leaving $D$
unconstrained. `Boolean::alloc` donates that spare `Extra` token
back to the allocator:

```rust,ignore
pub fn alloc<A: Allocator<'dr, D>>(
    dr: &mut D,
    allocator: &mut A,
    value: DriverValue<D, bool>,
) -> Result<Boolean<'dr, D>> {
    // ... constrains a * (1 - a) = 0 ...

    // The gate's spare D wire is donated to the allocator.
    allocator.donate(extra);

    Ok(Boolean { value, wire: a })
}
```

When using `PoolAllocator`, subsequent allocations redeem these
donated tokens at zero gate cost:

```rust,ignore
let allocator = &mut PoolAllocator::new();
let flag = Boolean::alloc(dr, allocator, bit)?;   // 1 gate
let x = Element::alloc(dr, allocator, witness)?;  // 0 gates (reuses donated D)
```

Like `SimpleAllocator`, `PoolAllocator` also pairs its own gate
allocations internally. When the pool is empty and a fresh gate is
needed, the spare `Extra` from that gate enters the pool for the
next call.

```admonish info
Dropping a `PoolAllocator` with tokens still in the pool is safe.
The driver already assigned $D = 0$ for those gates.
```

## Choosing an Allocator {#choosing}

| Situation | Allocator |
|-----------|-----------|
| Two or more consecutive allocations | [`SimpleAllocator`] |
| Allocations interleaved with boolean or other donating gadgets | [`PoolAllocator`] |
| Single isolated allocation | `()` |

[`SimpleAllocator`] is the right default whenever you allocate more
than one wire in sequence. Use [`PoolAllocator`] when your circuit
mixes allocations with gadgets that donate spare wires (like
[`Boolean::alloc`]). Use `()` when a single allocation is truly
standalone and introducing state would add unnecessary complexity.

## Cost Accounting {#cost-accounting}

The [`Simulator`] makes allocation costs visible. Compare two unit
allocations against one paired allocation:

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

In larger circuits, allocation costs compound quickly. Running the
[`Simulator`] before committing to a rank is the easiest way to
catch unnecessary gate overhead early.

[`gate()`]: ragu_core::drivers::DriverTypes::gate
[`mul()`]: ragu_core::drivers::Driver::mul
[`Allocator`]: ragu_primitives::allocator::Allocator
[`Element::alloc`]: ragu_primitives::Element::alloc
[`Driver::mul`]: ragu_core::drivers::Driver::mul
[`SimpleAllocator`]: ragu_primitives::allocator::SimpleAllocator
[`PoolAllocator`]: ragu_primitives::allocator::PoolAllocator
[assign-extra]: ragu_core::drivers::DriverTypes::assign_extra
[`Boolean::alloc`]: ragu_primitives::Boolean::alloc
[`Simulator`]: ragu_primitives::Simulator
