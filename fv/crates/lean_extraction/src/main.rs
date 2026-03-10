mod driver;
mod expr;
mod linexp;

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use ragu_core::drivers::Driver;

use driver::ExtractionDriver;
use expr::{Expr, Op};

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

fn main() {
    let mut dr = ExtractionDriver::<Fp>::new();

    // MaybeKind = Empty: the closure is never called.
    let assignment: ragu_core::maybe::Empty = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
    Point::<_, EpAffine>::alloc(&mut dr, assignment).expect("Point::alloc failed");

    println!("Point::alloc: {} operations", dr.ops.len());
    println!("def operations : Operations CircuitField := [");
    for op in &dr.ops {
        match op {
            Op::Witness {
                first_idx: _,
                count,
            } => {
                println!("  Operation.witness {count} (fun _env => default),");
            }
            Op::Assert(expr) => {
                println!("  Operation.assert ({}),", display_expr(expr));
            }
        }
    }
    println!("]");
}
