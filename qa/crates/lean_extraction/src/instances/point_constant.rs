use group::prime::PrimeCurveAffine;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct PointConstantInstance;

impl CircuitInstance for PointConstantInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Representative curve point: the Pallas generator. `Point::constant`
        // emits zero ops and just lifts the coordinates into constant wires.
        let point = Point::<_, EpAffine>::constant(dr, EpAffine::generator())?;
        WireCollector::collect_from(&point)
    }
}
