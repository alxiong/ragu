import Ragu.Circuits.Point.Endo
import Ragu.Instances.Autogen.Point.Endo
import Ragu.Core

namespace Ragu.Instances.Point.Endo
open Ragu.Instances.Autogen.Point.Endo

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Point.Spec.Point (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Point.Spec.Point
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Spec input output :=
    input.isOnCurve Circuits.Point.Spec.EpAffineParams →
    (output = Circuits.Point.Spec.Point.endo input Circuits.Point.Spec.EpAffineParams
      ∧ output.isOnCurve Circuits.Point.Spec.EpAffineParams)

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Point.Spec.Point Circuits.Point.Spec.Point
      (Circuits.Point.Endo.circuit Circuits.Point.Spec.EpAffineParams)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      Circuits.Point.Endo.circuit, Circuits.Point.Endo.elaborated, Circuits.Point.Endo.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.Endo.circuit, Circuits.Point.Endo.elaborated, Circuits.Point.Endo.main]
    show Expression.mul _ _ = Expression.mul _ _
    congr 1
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Point.Endo.circuit, Circuits.Point.Endo.Assumptions,
      Circuits.Point.Endo.Spec]
    rfl

end Ragu.Instances.Point.Endo
