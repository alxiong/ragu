use group::prime::PrimeCurveAffine;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{Boolean, Point};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct PointConditionalNegateInstance;

impl CircuitInstance for PointConditionalNegateInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond = Boolean::promote(
            cond_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );

        let template = Point::constant(dr, EpAffine::generator())?;
        let input_point = WireDeserializer::new(point_wires).into_gadget(&template)?;

        // `conditional_negate` is composite: `self.y.negate()` (virtual),
        // `condition.conditional_select(self.y, neg_y)` (one mul gate + 2
        // enforce_equals), then reassembles into a Point with the original x
        // and the selected y. Emits 3 wires + 3 asserts.
        let result = input_point.conditional_negate(dr, &cond)?;

        WireCollector::collect_from(&result)
    }
}
