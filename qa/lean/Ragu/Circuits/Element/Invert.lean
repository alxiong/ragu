import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Invert
variable {p : ℕ} [Fact p.Prime]

/-- `Element::invert(input)` computes `1/input` internally and delegates to
`invert_with`. Under `MaybeKind = Empty`, the inverse-computation closure is
erased, so the emitted trace is identical to invert_with's: one mul gate
with `a = input`, `c = 1`, and `b = 1/input` as the output wire. -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (input : Expression (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, b, c⟩ ← Core.AllocMul.circuit hintReader ()
  assertZero (a - input)
  assertZero (c - 1)
  return b

/-- Stronger than `invert_with`: the caller must promise `input ≠ 0`
(otherwise the inverse doesn't exist and the honest prover can't satisfy
the constraint `b · input = 1`). -/
def Assumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : F p) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  r.x = input ∧ r.x * r.y = 1 ∧ input ≠ 0

def Spec (input : F p) (out : F p) (_data : ProverData (F p)) :=
  input * out = 1

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) field field where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_a, h_c⟩ := h_holds
  rw [add_neg_eq_zero] at h_a h_c
  rw [h_a, h_c] at h_mul
  exact h_mul

theorem completeness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (Assumptions hintReader) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  obtain ⟨h_x_in, h_prod_in, _⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_x_eq]; exact h_x_in
  · rw [h_z_eq]; exact h_prod_in

def circuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) field field :=
  { elaborated hintReader with
    Assumptions := Assumptions hintReader,
    Spec := Spec,
    soundness := soundness hintReader,
    completeness := completeness hintReader }

end Ragu.Circuits.Element.Invert
