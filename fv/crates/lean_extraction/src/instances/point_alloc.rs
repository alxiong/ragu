use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use crate::driver::ExtractionDriver;
use crate::expr::Expr;
use crate::instance::{CircuitInstance, WireCollector};

pub struct PointAllocInstance;

impl CircuitInstance for PointAllocInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the closure is never called.
        let assignment = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
        let point = Point::<_, EpAffine>::alloc(dr, assignment)?;

        // NOTE: assumes that the serialization is [x, y].
        // TODO: This is an assumption we should not make in general, and would be better if we "manually"
        // serialize the output into a Vector. However, Point wires are private, so this is the only way
        // for now
        WireCollector::collect_from(&point)
    }
}
