import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.ConditionalSelect
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::conditional_select(a, b)` emits one mul gate producing
`cond * (b - a)`, with the two factor wires constrained via
`enforce_equal` to `cond` and `b - a` respectively. The returned
element is the virtual expression `a + cond * (b - a)`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let cv := Expression.eval env input.cond
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    (⟨cv, bv - av, cv * (bv - av)⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.cond)
  assertZero (y - (input.b - input.a))
  return input.a + z

/-- Caller must promise `cond` is boolean; the algebraic `Spec` holds
regardless, but is only meaningful as a "select" under this precondition. -/
def Assumptions (input : Input (F p)) :=
  input.cond = 0 ∨ input.cond = 1

/-- Matches the Rust formula: `out = a + cond * (b - a)`. Under the boolean
assumption this simplifies to `a` (when `cond = 0`) or `b` (when `cond = 1`). -/
def Spec (input : Input (F p)) (out : F p) :=
  out = input.a + input.cond * (input.b - input.a)

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
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

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.ConditionalSelect
