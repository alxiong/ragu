import Clean.Circuit
import Ragu.Circuits.Core.AllocMul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.ConditionalNegate
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  x : F
  y : F
deriving ProvableStruct

/-- `Point::conditional_negate(cond)` is a composite: `self.y.negate()`
(virtual), then `cond.conditional_select(self.y, -self.y)` (one mul gate +
2 enforce_equals), then reassemble as a Point with the unchanged x and the
selected y. Emits 3 wires + 3 asserts. -/
def main (input : Var Input (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x1, yw, z⟩ ← (witness fun env =>
    let cv := Expression.eval env input.cond
    let yv := Expression.eval env input.y
    let diff := -yv - yv  -- neg_y - y = -y - y = -2y
    (⟨cv, diff, cv * diff⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x1 * yw - z)
  assertZero (x1 - input.cond)
  assertZero (yw - (-input.y - input.y))
  return ⟨input.x, input.y + z⟩

/-- Caller must promise `cond ∈ {0, 1}`; the algebraic `Spec` holds
unconditionally, but is only meaningful as a "conditional negate" under
this precondition. -/
def Assumptions (input : Input (F p)) :=
  input.cond = 0 ∨ input.cond = 1

/-- Matches the Rust formula: new y is `y + cond · (-y - y)` and the x is
unchanged. Under `cond = 0` the y is unchanged; under `cond = 1` the y
becomes `-y`. -/
def Spec (input : Input (F p)) (output : Spec.Point (F p)) :=
  output.x = input.x ∧
  output.y = input.y + input.cond * (-input.y - input.y)

instance elaborated : ElaboratedCircuit (F p) Input Spec.Point where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  -- Only the y-equation remains; x = input.x is closed by rfl.
  rw [← c1, c2, c3]
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;> ring

def circuit : FormalCircuit (F p) Input Spec.Point :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Point.ConditionalNegate
