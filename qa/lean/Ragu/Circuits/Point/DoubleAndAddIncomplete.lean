import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.DoubleAndAddIncomplete
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  P1 : Spec.Point F  -- the point to be doubled (Rust's `self`)
  P2 : Spec.Point F  -- the point to be added once (Rust's `other`)
deriving ProvableStruct

/-- `Point::double_and_add_incomplete(other)` computes `2·P1 + P2` via the
zcash optimization that avoids materializing `P1 + P2` explicitly:

- λ₁ = (y₂ - y₁) / (x₂ - x₁) — slope through P1 and P2.
- x_r = λ₁² - x₁ - x₂ — x-coord of P1 + P2.
- λ₂ = 2y₁ / (x₁ - x_r) - λ₁ — slope through (P1 + P2) and P1 (derived).
- x_s = λ₂² - x_r - x₁.
- y_s = λ₂ (x₁ - x_s) - y₁.

Result: (x_s, y_s) = 2·P1 + P2. Two DivNonzero subcircuits (one hint each)
+ two Square subcircuits + one Mul subcircuit = 15 wires. -/
def main (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
         (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : Var Inputs (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := input

  -- λ₁ = (y₂ - y₁) / (x₂ - x₁)
  let tmp1 := x2 - x1
  let lambda_1 ← Element.DivNonzero.generalCircuit hintReader1 ⟨y2 - y1, tmp1⟩

  -- x_r = λ₁² - x₁ - x₂
  let lambda_1_sq ← subcircuit Element.Square.circuit lambda_1
  let x_r := lambda_1_sq - x1 - x2

  -- λ₂ = 2y₁ / (x₁ - x_r) - λ₁
  let tmp2 := x1 - x_r
  let lambda_2_half ← Element.DivNonzero.generalCircuit hintReader2 ⟨y1 + y1, tmp2⟩
  let lambda_2 := lambda_2_half - lambda_1

  -- x_s = λ₂² - x_r - x₁
  let lambda_2_sq ← subcircuit Element.Square.circuit lambda_2
  let x_s := lambda_2_sq - x_r - x1

  -- y_s = λ₂ (x₁ - x_s) - y₁
  let lambda_2_x_diff ← subcircuit Element.Mul.circuit ⟨lambda_2, x1 - x_s⟩
  let y_s := lambda_2_x_diff - y1

  return ⟨x_s, y_s⟩

/-- Completeness needs both DivNonzero hints to describe valid witnesses
(quotient and denominator agree with the respective inputs) and the two
intermediate non-degeneracies: `x₁ ≠ x₂` (for the first slope) and
`x₁ ≠ x_r` (for the second slope, after computing the midpoint
x-coordinate). `x₁ ≠ x₂` is asserted here directly because the first
DivNonzero's `GeneralAssumptions` gives only the weaker `x₂-x₁ ≠ 0 ∨
y₂-y₁ = 0`, which isn't enough to discharge DivNonzero's `Spec` premise
when bridging the symbolic quotient to the witness. -/
def Assumptions (_curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : Inputs (F p)) (data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let x_r := ((input.P2.y - input.P1.y) / (input.P2.x - input.P1.x))^2
    - input.P1.x - input.P2.x
  input.P1.x ≠ input.P2.x ∧
  Element.DivNonzero.GeneralAssumptions hintReader1
    ⟨input.P2.y - input.P1.y, input.P2.x - input.P1.x⟩ data hint ∧
  Element.DivNonzero.GeneralAssumptions hintReader2
    ⟨input.P1.y + input.P1.y, input.P1.x - x_r⟩ data hint

/-- The output is `2·P1 + P2` under the curve-membership preconditions and
the two non-degeneracy assumptions. Stated via `add_incomplete` twice:
`r = P1 + P2`, then `s = r + P1 = 2P1 + P2`. -/
def Spec (curveParams : Spec.CurveParams p) (input : Inputs (F p))
    (output : Spec.Point (F p)) (_data : ProverData (F p)) :=
  input.P1.isOnCurve curveParams →
  input.P2.isOnCurve curveParams →
  input.P1.x ≠ input.P2.x →
  (match input.P1.add_incomplete input.P2 with
   | none => False
   | some r =>
     r.x ≠ input.P1.x →
     ((match r.add_incomplete input.P1 with
       | none => False
       | some s => output = s)
      ∧ output.isOnCurve curveParams))

instance elaborated (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) Inputs Spec.Point where
  main := main hintReader1 hintReader2
  localLength _ := 15

-- TODO: soundness proof. Setup is in place (completeness now closed):
--   - h_holds: five subcircuit specs (DivNonzero, Square, DivNonzero,
--     Square, Mul), destructured as c1..c5.
--   - c1 specialized with `Or.inl h_xne'` yields
--     `eval λ₁ = (y₂-y₁)/(x₂-x₁)`.
-- Remaining work: chain the five spec rewrites to express `output` as
-- `(Spec.Point.add_incomplete (Spec.Point.add_incomplete P1 P2) P1)`,
-- then close via `Lemmas.add_incomplete_preserves_membership` applied
-- twice (membership for `P1 + P2` = r, then for `r + P1` = output).
-- May need a dedicated helper lemma analogous to the existing one.
set_option maxHeartbeats 800000 in
theorem soundness (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader1 hintReader2)
        (Spec curveParams) := by
  sorry

set_option maxHeartbeats 800000 in
theorem completeness (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader1 hintReader2)
        (Assumptions curveParams hintReader1 hintReader2) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.generalCircuit, Element.DivNonzero.GeneralAssumptions,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  simp only [Element.DivNonzero.GeneralSpec] at h_env
  simp only [sub_eq_add_neg] at h_assumptions
  obtain ⟨h_xne, h_a1, h_a2⟩ := h_assumptions
  obtain ⟨h_div1_spec, h_sq1_spec, _⟩ := h_env
  -- Discharge DivNonzero#1's outer `Assumptions → ...` via h_a1, then its
  -- inner `(y ≠ 0 ∨ x ≠ 0) → out = x/y` via `x₁ ≠ x₂`.
  have h_div1 := h_div1_spec h_a1
  have h_prem : input_P2_x + -input_P1_x ≠ 0 ∨ input_P2_y + -input_P1_y ≠ 0 := by
    left
    intro h
    rw [add_neg_eq_zero] at h
    exact h_xne h.symm
  have h_div1_eq := h_div1.1 h_prem
  simp only [Element.Square.Spec] at h_sq1_spec
  -- Goal: (hint1 GeneralAssumptions) ∧ (hint2 GeneralAssumptions at env x_r).
  -- First conjunct is `h_a1` directly; second needs the env-level
  -- `Square(lambda_1)` → `lambda_1^2` → `((y2-y1)/(x2-x1))^2` rewrite chain.
  rw [h_sq1_spec, h_div1_eq]
  exact ⟨h_a1, h_a2⟩

def circuit (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) Inputs Spec.Point :=
  { elaborated hintReader1 hintReader2 with
    Assumptions := Assumptions curveParams hintReader1 hintReader2,
    Spec := Spec curveParams,
    soundness := soundness curveParams hintReader1 hintReader2,
    completeness := completeness curveParams hintReader1 hintReader2 }

end Ragu.Circuits.Point.DoubleAndAddIncomplete
