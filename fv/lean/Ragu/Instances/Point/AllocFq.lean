import Ragu.Circuits.Point.Alloc
import Ragu.Instances.Autogen.Point.AllocFq
import Ragu.Core

namespace Ragu.Instances.Point.AllocFq
open Ragu.Instances.Autogen.Point.AllocFq

set_option linter.unusedVariables false in
def deserializeInput (input : Var (ProvableVector field inputLen) (F p)) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) outputLen :=
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

  Input := unit
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Assumptions input := True
  Spec input output := output.isOnCurve Circuits.Point.Spec.EqAffineParams

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EqAffineParams

  same_circuit := by
    intro input
    simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
      Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by intro input; rfl
  same_spec := by intro input output; rfl
  same_assumptions := by intro input; rfl

end Ragu.Instances.Point.AllocFq
