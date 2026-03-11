use core::marker::PhantomData;

use ff::Field;
use ragu_core::convert::WireMap;
use ragu_core::gadgets::Gadget;

use crate::driver::ExtractionDriver;
use crate::expr::Expr;

/// A [`WireMap`] that collects all physical wires from a gadget by cloning
/// them into a flat [`Vec`].
///
/// Used by [`CircuitInstance`] implementors to manually serialize the output
/// of a circuit into a list of driver wires.
pub struct WireCollector<F: Field> {
    pub wires: Vec<Expr<F>>,
}

impl<F: Field> WireCollector<F> {
    pub fn new() -> Self {
        WireCollector { wires: Vec::new() }
    }

    pub fn collect_from<'dr, G>(gadget: &G) -> ragu_core::Result<Vec<Expr<F>>>
    where
        G: Gadget<'dr, ExtractionDriver<F>>,
        ExtractionDriver<F>: ragu_core::drivers::Driver<'dr, F = F>,
    {
        let mut collector = Self::new();
        gadget.map(&mut collector)?;
        Ok(collector.wires)
    }
}

impl<F: Field> WireMap<F> for WireCollector<F> {
    type Src = ExtractionDriver<F>;
    type Dst = PhantomData<F>;

    fn convert_wire(&mut self, wire: &Expr<F>) -> ragu_core::Result<()> {
        self.wires.push(wire.clone());
        Ok(())
    }
}

/// A trait for circuit instances that can be extracted by the driver.
pub trait CircuitInstance {
    type Field: Field + std::fmt::Debug;

    /// Run the circuit on `dr` and return its output.
    /// The output is a vector of expressions corresponding to the
    /// output wires in order. This must include all "interesting" wires for which we
    /// want to prove some properties about.
    /// They have to be physical wires (i.e. `Expr::Var`) since virtual wires cannot be
    /// referenced from outside the circuit.
    fn circuit(dr: &mut ExtractionDriver<Self::Field>)
    -> ragu_core::Result<Vec<Expr<Self::Field>>>;
}
