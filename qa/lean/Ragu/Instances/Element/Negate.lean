import Ragu.Circuits.Element.Negate
import Ragu.Instances.Autogen.Element.Negate
import Ragu.Core

namespace Ragu.Instances.Element.Negate
open Ragu.Instances.Autogen.Element.Negate

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

  deserializeInput
  serializeOutput

  Spec (input : F p) (output : F p) := output = -input

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      Circuits.Element.Negate.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Negate.circuit, Circuits.Element.Negate.elaborated, Circuits.Element.Negate.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Negate.circuit, Circuits.Element.Negate.elaborated, Circuits.Element.Negate.main]
    show Expression.mul _ _ = Expression.mul _ _
    congr 1
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Negate.circuit, Circuits.Element.Negate.Assumptions,
      Circuits.Element.Negate.Spec]
    aesop

end Ragu.Instances.Element.Negate
