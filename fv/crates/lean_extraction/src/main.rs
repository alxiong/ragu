mod driver;
mod expr;
mod instance;
mod instances;
mod linexp;

use ff::Field;
use ragu_arithmetic::Coeff;

use driver::ExtractionDriver;
use expr::{Expr, Op};
use instance::CircuitInstance;
use instances::point_alloc::PointAllocInstance;

fn display_coeff<F: Field + std::fmt::Debug>(c: &Coeff<F>) -> String {
    match c {
        Coeff::Zero => "0".to_owned(),
        Coeff::One => "1".to_owned(),
        Coeff::Two => "2".to_owned(),
        Coeff::NegativeOne => format!("{:?}", F::ONE.neg()),
        Coeff::Arbitrary(f) => format!("{f:?}"),
        Coeff::NegativeArbitrary(f) => format!("-({f:?})"),
    }
}

fn display_expr<F: Field + std::fmt::Debug>(expr: &Expr<F>) -> String {
    match expr {
        Expr::Var(i) => {
            if *i == 0 {
                // var at 0 is the ONE wire
                "1".to_owned()
            } else {
                // everything else is a proper variable in the circuit,
                // we re-index to start at 0
                let var_index = i - 1;
                format!("(var {var_index})")
            }
        }
        Expr::Const(c) => display_coeff(c),
        Expr::Add(l, r) => format!("({} + {})", display_expr(l), display_expr(r)),
        Expr::Mul(l, r) => format!("({} * {})", display_expr(l), display_expr(r)),
    }
}

fn print_output_indices<F: Field + std::fmt::Debug>(wires: &[Expr<F>]) {
    // Re-index: wire 0 is the ONE wire, allocations start at 1, so var N = wire N+1.
    print!("def exported_output : List (Expression CircuitField) := [");
    for (i, wire) in wires.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        match wire {
            Expr::Var(idx) => print!("(var {})", idx - 1),
            _ => panic!("output wire is not a physical wire (Expr::Var)"),
        }
    }
    println!("]");
}

fn main() {
    let mut dr = ExtractionDriver::<<PointAllocInstance as CircuitInstance>::Field>::new();

    let wires = PointAllocInstance::circuit(&mut dr).expect("circuit failed");

    println!("Point::alloc: {} operations", dr.ops.len());
    println!("def exported_operations : Operations CircuitField := [");
    for op in &dr.ops {
        match op {
            Op::Witness { count } => {
                println!("  Operation.witness {count} (fun _env => default),");
            }
            Op::Assert(expr) => {
                println!("  Operation.assert ({}),", display_expr(expr));
            }
        }
    }
    println!("]\n");

    print_output_indices(&wires);
}
