import Ragu.Circuits.Point.Double
import Ragu.Instances.Autogen.Point.Double
import Ragu.Core

namespace Ragu.Instances.Point.Double
open Ragu.Instances.Autogen.Point.Double

def deserializeInput (input : Var (ProvableVector field inputLen) (F p)) : Var Circuits.Point.Spec.Point (F p) :=
  {
    x := input.get 0,
    y := input.get 1
  }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[
    output.x,
    output.y
  ]

def formal_instance : Core.Statements.FormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Point.Spec.Point
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Assumptions input :=
    input.isOnCurve Circuits.Point.Spec.EpAffineParams ∧
    Circuits.Point.Spec.EpAffineParams.noOrderTwoPoints

  Spec input output :=
    (match input.double with
    | none => False
    | some double => output = double)
    ∧
    output.isOnCurve Circuits.Point.Spec.EpAffineParams

  reimplementation := Circuits.Point.Double.circuit Circuits.Point.Spec.EpAffineParams

  same_circuit := by
    intro input
    simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    constructor <;> rfl
  same_spec := by
    intro input output
    simp [Circuits.Point.Double.circuit, Circuits.Point.Double.Spec]
    intro h1
    aesop
  same_assumptions := by intro input; rfl

end Ragu.Instances.Point.Double
