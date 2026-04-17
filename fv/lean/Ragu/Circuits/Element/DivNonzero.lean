import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (input : Var Inputs (F p))
    : Circuit (F p) (Core.AllocMul.Row (F p)) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit ()
  assertZero (input.x - numerator)
  assertZero (input.y - denominator)
  return quotient

def GeneralAssumptions
    (input : Inputs (F p)) (_data : ProverData (F p)) (hint : Core.AllocMul.Row (F p)) :=
  hint.y = input.y ∧ hint.x * hint.y = input.x ∧ (input.y ≠ 0 ∨ input.x = 0)

def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0 → out = input.x / input.y

instance elaborated : ElaboratedCircuit (F p) (Core.AllocMul.Row (F p)) Inputs field where
  main
  localLength _ := 3

theorem generalSoundness
    : GeneralFormalCircuit.Soundness (F p) (Core.AllocMul.Row (F p)) elaborated GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_x, h_y⟩ := h_holds
  rw [add_neg_eq_zero] at h_x h_y
  intro h_y_ne
  grind

theorem generalCompleteness
    : GeneralFormalCircuit.Completeness (F p) (Core.AllocMul.Row (F p)) elaborated GeneralAssumptions := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_y_in, h_z_in, _⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_z_eq]; exact h_z_in.symm
  · rw [h_y_eq]; exact h_y_in.symm

def generalCircuit
    : GeneralFormalCircuit (F p) (Core.AllocMul.Row (F p)) Inputs field :=
  { elaborated with
    Assumptions := GeneralAssumptions,
    Spec := GeneralSpec,
    soundness := generalSoundness,
    completeness := generalCompleteness }

end Ragu.Circuits.Element.DivNonzero
