use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_pasta::{Fp, Fq};

use crate::expr::{Expr, Op};

pub trait FieldExporter: Field {
    fn get_field_definition() -> &'static str;
}

impl FieldExporter for Fp {
    fn get_field_definition() -> &'static str {
        "def p := Core.Primes.p"
    }
}

impl FieldExporter for Fq {
    fn get_field_definition() -> &'static str {
        "def p := Core.Primes.q"
    }
}

fn display_coeff<F: Field + std::fmt::Debug>(c: &Coeff<F>) -> String {
    match c {
        Coeff::Zero => "0".to_owned(),
        Coeff::One => "1".to_owned(),
        Coeff::Two => "2".to_owned(),
        Coeff::NegativeOne => format!("({:?} : Expression CircuitField)", F::ONE.neg()),
        Coeff::Arbitrary(f) => format!("({f:?} : Expression CircuitField)"),
        Coeff::NegativeArbitrary(f) => format!("({:?} : Expression CircuitField)", f.neg()),
    }
}

fn display_expr<F: Field + std::fmt::Debug>(expr: &Expr<F>) -> String {
    match expr {
        Expr::Var(i) => {
            if *i == 0 {
                "1".to_owned()
            } else {
                format!("(var {})", i - 1)
            }
        }
        Expr::InputVar(i) => format!("(input_var.get {i})"),
        Expr::Const(c) => display_coeff(c),
        Expr::Add(l, r) => format!("({} + {})", display_expr(l), display_expr(r)),
        Expr::Mul(l, r) => format!("({} * {})", display_expr(l), display_expr(r)),
    }
}

pub fn render_field_definition<F: FieldExporter>() -> String {
    format!("@[reducible]\n{}\n", F::get_field_definition())
}

pub fn render_exported_operations<F: Field + std::fmt::Debug>(ops: &[Op<F>]) -> String {
    let mut output = String::from(
        "set_option linter.unusedVariables false in\n\
def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := [\n",
    );

    for op in ops {
        match op {
            Op::Witness { count } => {
                output.push_str(&format!(
                    "  Operation.witness {count} (fun _env => default),\n"
                ));
            }
            Op::Assert(expr) => {
                output.push_str(&format!("  Operation.assert ({}),\n", display_expr(expr)));
            }
        }
    }

    output.push(']');
    output.push('\n');
    output
}

pub fn render_exported_output<F: Field + std::fmt::Debug>(wires: &[Expr<F>]) -> String {
    let mut output = format!(
        "set_option linter.unusedVariables false in\n\
@[reducible]\n\
def exported_output (input_var : Var Inputs CircuitField) : Vector (Expression CircuitField) {} := #v[\n",
        wires.len()
    );

    for expr in wires {
        output.push_str(&format!("  {},\n", display_expr(expr)));
    }

    output.push(']');
    output.push('\n');
    output
}
