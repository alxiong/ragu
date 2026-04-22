import Ragu.Circuits.Boolean.Multipack
import Ragu.Instances.Autogen.Boolean.Multipack
import Ragu.Core

namespace Ragu.Instances.Boolean.Multipack
open Ragu.Instances.Autogen.Boolean.Multipack

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.Multipack.Input (F p) :=
  { b0 := input[0], b1 := input[1], b2 := input[2] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Boolean.Multipack.Input
  Output := field

  Spec (input : Circuits.Boolean.Multipack.Input (F p)) (output : F p) :=
    ((input.b0 = 0 ∨ input.b0 = 1) ∧ (input.b1 = 0 ∨ input.b1 = 1) ∧ (input.b2 = 0 ∨ input.b2 = 1))
      → output = input.b0 + 2 * input.b1 + 4 * input.b2

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Boolean.Multipack.Input field
      Circuits.Boolean.Multipack.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.Multipack.circuit,
      Circuits.Boolean.Multipack.elaborated,
      Circuits.Boolean.Multipack.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.Multipack.circuit,
      Circuits.Boolean.Multipack.elaborated,
      Circuits.Boolean.Multipack.main]
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Boolean.Multipack.circuit,
      Circuits.Boolean.Multipack.Assumptions,
      Circuits.Boolean.Multipack.Spec]
    aesop

end Ragu.Instances.Boolean.Multipack
