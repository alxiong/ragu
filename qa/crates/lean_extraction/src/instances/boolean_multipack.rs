use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::{Boolean, multipack};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct BooleanMultipackInstance;

impl CircuitInstance for BooleanMultipackInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Length 3 is a representative choice for the variadic `multipack`.
        // For `F::CAPACITY = 254`, all three bits fit in a single chunk, so
        // the output is a single packed `Element`.
        let b0_wires = dr.alloc_input_wires(1);
        let b1_wires = dr.alloc_input_wires(1);
        let b2_wires = dr.alloc_input_wires(1);

        let b0 = Boolean::promote(b0_wires[0].clone(), ExtractionDriver::<Fp>::just(|| false));
        let b1 = Boolean::promote(b1_wires[0].clone(), ExtractionDriver::<Fp>::just(|| false));
        let b2 = Boolean::promote(b2_wires[0].clone(), ExtractionDriver::<Fp>::just(|| false));

        // `multipack` is "free" in the circuit model: every wire is built via
        // `dr.add` (virtual), and `Element::promote` wraps without emitting ops.
        // The returned `Element`'s wire is the LE-packed linear combination
        // `b0 + 2·b1 + 4·b2`.
        let result = multipack(dr, &[b0, b1, b2])?;

        WireCollector::collect_from(&result[0])
    }
}
