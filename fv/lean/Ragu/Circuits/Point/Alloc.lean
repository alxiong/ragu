import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- Hint for `Point.Alloc`: the x and y coordinates the prover allocates. -/
structure Hint (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (curveParams : Spec.CurveParams p)
    (_input : Unit) : Circuit (F p) (Hint (F p)) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.generalCircuit (fun h : Hint (F p) => h.x) ()
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.generalCircuit (fun h : Hint (F p) => h.y) ()
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (curveParams : Spec.CurveParams p)
    (_input : Unit) (_data : ProverData (F p)) (hint : Hint (F p)) :=
  hint.x ^ 3 + curveParams.b = hint.y ^ 2

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p)
    : ElaboratedCircuit (F p) (Hint (F p)) unit Spec.Point where
  main := main curveParams
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit.Soundness (F p) (Hint (F p)) (elaborated curveParams) (Spec curveParams) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  simp only [Spec.Point.isOnCurve]
  obtain ⟨h_sq_x, h_mul, h_sq_y, h_assert⟩ := h_holds
  rw [add_neg_eq_zero, mul_one] at h_assert
  rw [← h_sq_y, ← h_assert, h_mul, h_sq_x]
  ring

theorem completeness (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit.Completeness (F p) (Hint (F p)) (elaborated curveParams)
      (Assumptions curveParams) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec, Element.AllocSquare.CompletenessSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, _, h_ysq⟩⟩ := h_env
  rw [h_mul, h_x, h_xsq, h_ysq, mul_one, add_neg_eq_zero]
  rw [show hint_x * hint_x ^ 2 = hint_x ^ 3 from by ring]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit (F p) (Hint (F p)) unit Spec.Point :=
  {
    (elaborated curveParams) with
    Assumptions := Assumptions curveParams,
    Spec := (Spec curveParams),
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.Alloc
