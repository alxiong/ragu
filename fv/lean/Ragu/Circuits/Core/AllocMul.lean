import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

def main (_input : Unit) : Circuit (F p) (Row (F p)) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun _env hint =>
    (⟨hint.x, hint.y, hint.x * hint.y⟩ : Row (F p))
    : Circuit (F p) (Row (F p)) (Var Row (F p)))
  assertZero (x * y - z)
  return ⟨x, y, z⟩

def Assumptions (_input : Unit) (_data : ProverData (F p)) (_hint : Row (F p)) := True

def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row matches the hint on `x`/`y`; `z` is always wired to `x * y`. -/
def CompletenessSpec (_input : Unit) (out : Row (F p)) (hint : Row (F p)) :=
  out.x = hint.x ∧ out.y = hint.y ∧ out.z = hint.x * hint.y

instance elaborated : ElaboratedCircuit (F p) (Row (F p)) unit Row where
  main
  localLength _ := 3

theorem soundness : GeneralFormalCircuit.Soundness (F p) (Row (F p)) elaborated Spec := by
  circuit_proof_start
  rw [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness : GeneralFormalCircuit.Completeness (F p) (Row (F p)) elaborated Assumptions := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  ring

theorem completenessSpec : GeneralFormalCircuit.CompletenessSpecProof (F p) (Row (F p)) elaborated Assumptions CompletenessSpec := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  exact ⟨h0, h1, h2⟩

def circuit : GeneralFormalCircuit (F p) (Row (F p)) unit Row :=
  { elaborated with
    Assumptions,
    Spec,
    CompletenessSpec,
    soundness,
    completeness,
    completenessSpec }

end Ragu.Circuits.Core.AllocMul
