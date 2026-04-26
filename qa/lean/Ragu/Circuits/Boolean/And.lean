import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.And
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::and` emits one mul gate (`x · y = z`) and two `enforce_equal`s
binding the gate's `x`/`y` wires to the input boolean wires. Returns the
gate's `z` wire as the output. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    (⟨av, bv, av * bv⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.a)
  assertZero (y - input.b)
  return z

/-- Caller must promise the inputs are boolean. -/
def Assumptions (input : Input (F p)) :=
  IsBool input.a ∧ IsBool input.b

/-- The output is the bitwise AND of the inputs (interpreted as `Nat`),
and is itself boolean-valued. Stated in `Bool`/`Nat` form rather than
field-multiplication form via `IsBool.and_eq_val_and`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out.val = input.a.val &&& input.b.val ∧ IsBool out

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  obtain ⟨ha, hb⟩ := h_assumptions
  -- c1 : env_x * env_y = env_z, c2 : env_x = input_a, c3 : env_y = input_b
  -- so env_z (= out) = input_a * input_b, and the spec follows from IsBool theorems.
  have h_out : env.get (i₀ + 1 + 1) = input_a * input_b := by rw [←c2, ←c3, c1]
  refine ⟨?_, ?_⟩
  · rw [h_out]; exact IsBool.and_eq_val_and ha hb
  · rw [h_out]; exact IsBool.and_is_bool ha hb

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

end Ragu.Circuits.Boolean.And
