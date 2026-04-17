import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]
variable {ProverHint : Type}

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) ProverHint (Var field (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env _hint =>
    let xv := Expression.eval env input.x
    let yv := Expression.eval env input.y
    ⟨xv, yv, xv * yv⟩
    : Circuit (F p) ProverHint (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (out : field (F p)) :=
  out = input.x * input.y

instance elaborated : ElaboratedCircuit (F p) ProverHint Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) ProverHint elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  rw [←c2, ←c3, c1]

theorem completeness : Completeness (F p) ProverHint elaborated Assumptions := by
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

def circuit : FormalCircuit (F p) ProverHint Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Mul
