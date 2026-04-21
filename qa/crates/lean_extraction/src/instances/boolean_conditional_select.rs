use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::{Boolean, Element};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct BooleanConditionalSelectInstance;

impl CircuitInstance for BooleanConditionalSelectInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond = Boolean::promote(
            cond_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );

        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        // `conditional_select` is a composite: `b.sub(a)` (virtual),
        // `cond.element().mul(diff)` (one mul gate + 2 enforce_equals),
        // `a.add(cond_times_diff)` (virtual).
        let result = cond.conditional_select(dr, &a, &b)?;

        WireCollector::collect_from(&result)
    }
}
