import Ragu.Circuits.Boolean.Not
import Ragu.Instances.Autogen.Boolean.Not
import Ragu.Core

namespace Ragu.Instances.Boolean.Not
open Ragu.Instances.Autogen.Boolean.Not

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := field
  Output := field

  Spec (input : F p) (output : F p) :=
    (input = 0 ∨ input = 1) → output = 1 - input

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      Circuits.Boolean.Not.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.Not.circuit,
      Circuits.Boolean.Not.elaborated,
      Circuits.Boolean.Not.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.Not.circuit,
      Circuits.Boolean.Not.elaborated,
      Circuits.Boolean.Not.main]
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Boolean.Not.circuit,
      Circuits.Boolean.Not.Assumptions,
      Circuits.Boolean.Not.Spec]
    aesop

end Ragu.Instances.Boolean.Not
