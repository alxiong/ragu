mod codegen;
mod driver;
mod expr;
mod instance;
mod instances;
mod linexp;

use std::path::PathBuf;

use instance::CircuitInstance;

use crate::instances::{
    point_add::PointAddInstance, point_alloc::PointAllocInstanceFp,
    point_alloc::PointAllocInstanceFq, point_double::PointDoubleInstance,
    point_neg::PointNegInstance,
};

fn default_autogen_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean")
}

fn main() -> std::io::Result<()> {
    let autogen_root = default_autogen_root();

    for (name, path) in [
        (
            "Ragu.Instances.Autogen.Point.AllocFp",
            PointAllocInstanceFp::export("Ragu.Instances.Autogen.Point.AllocFp", &autogen_root)?,
        ),
        (
            "Ragu.Instances.Autogen.Point.AllocFq",
            PointAllocInstanceFq::export("Ragu.Instances.Autogen.Point.AllocFq", &autogen_root)?,
        ),
        (
            "Ragu.Instances.Autogen.Point.Negate",
            PointNegInstance::export("Ragu.Instances.Autogen.Point.Negate", &autogen_root)?,
        ),
        (
            "Ragu.Instances.Autogen.Point.Double",
            PointDoubleInstance::export("Ragu.Instances.Autogen.Point.Double", &autogen_root)?,
        ),
        (
            "Ragu.Instances.Autogen.Point.AddIncomplete",
            PointAddInstance::export("Ragu.Instances.Autogen.Point.AddIncomplete", &autogen_root)?,
        ),
    ] {
        println!("wrote {name} to {}", path.display());
    }

    Ok(())
}
