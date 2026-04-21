use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Boolean;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct BooleanNotInstance;

impl CircuitInstance for BooleanNotInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        // `Boolean::promote` wraps an already-allocated boolean wire with no
        // circuit cost. The caller (here: the Lean spec via `Assumptions`)
        // must ensure the wire is boolean-constrained upstream.
        let value = ExtractionDriver::<Fp>::just(|| false);
        let boolean = Boolean::promote(input_wires[0].clone(), value);

        // `Boolean::not` emits no ops — it just produces a new wire expression
        // `1 - self.wire()`.
        let negated = boolean.not(dr);

        WireCollector::collect_from(&negated)
    }
}
