import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]
variable {ProverHint : Type}

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

/-- Allocate a square. Takes a `proj : ProverHint → F p` so that callers can
    reuse this circuit within a larger `ProverHint` context by projecting out
    the specific field the prover supplies. -/
def main (proj : ProverHint → F p) (_input : Unit) : Circuit (F p) ProverHint (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun _env (h : ProverHint) =>
    let a := proj h
    (⟨a, a, a * a⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) ProverHint (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_proj : ProverHint → F p)
    (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def CompletenessSpec (proj : ProverHint → F p)
    (_input : Unit) (out : Square (F p)) (hint : ProverHint) :=
  out.a = proj hint ∧ out.a_sq = (proj hint)^2

instance elaborated (proj : ProverHint → F p) : ElaboratedCircuit (F p) ProverHint unit Square where
  main := main proj
  localLength _ := 3

theorem soundness (proj : ProverHint → F p) :
    GeneralFormalCircuit.Soundness (F p) ProverHint (elaborated proj) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  rw [←c1, c2]
  ring

theorem completeness (proj : ProverHint → F p) :
    GeneralFormalCircuit.Completeness (F p) ProverHint (elaborated proj) (Assumptions proj) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_⟩ <;> ring

theorem completenessSpec (proj : ProverHint → F p) :
    GeneralFormalCircuit.CompletenessSpecProof (F p) ProverHint (elaborated proj)
      (Assumptions proj) (CompletenessSpec proj) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.reduceAdd, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  refine ⟨h0, ?_⟩
  rw [h2]; ring

def generalCircuit (proj : ProverHint → F p) :
    GeneralFormalCircuit (F p) ProverHint unit Square :=
  { elaborated proj with
    Assumptions := Assumptions proj,
    Spec,
    CompletenessSpec := CompletenessSpec proj,
    soundness := soundness proj,
    completeness := completeness proj,
    completenessSpec := completenessSpec proj }

end Ragu.Circuits.Element.AllocSquare
