import Ragu.Circuits.Element.Sub
import Ragu.Instances.Autogen.Element.Sub
import Ragu.Core

namespace Ragu.Instances.Element.Sub
open Ragu.Instances.Autogen.Element.Sub

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.Sub.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Sub.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = input.x - input.y

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Sub.Input field
      Circuits.Element.Sub.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Sub.circuit, Circuits.Element.Sub.elaborated, Circuits.Element.Sub.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Sub.circuit, Circuits.Element.Sub.elaborated, Circuits.Element.Sub.main]
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Sub.circuit, Circuits.Element.Sub.Assumptions,
      Circuits.Element.Sub.Spec]
    aesop

end Ragu.Instances.Element.Sub
