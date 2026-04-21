import Clean.Circuit

namespace Ragu.Circuits.Element.EnforceZero
variable {p : ℕ} [Fact p.Prime]

def main (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  assertZero input

/-- The caller must promise the input is zero. Without this, the honest
prover cannot satisfy the `assertZero` constraint — completeness fails. -/
def Assumptions (input : F p) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := input = 0

/-- If the constraint holds, the input equals zero — this is what the
verifier learns. Stated independently of `Assumptions` so the soundness
claim is non-tautological. -/
def Spec (input : F p) (_output : Unit) (_data : ProverData (F p)) :=
  input = 0

instance elaborated : ElaboratedCircuit (F p) field unit where
  main
  localLength _ := 0

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Spec := by
  circuit_proof_start
  exact h_holds

theorem completeness : GeneralFormalCircuit.Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  exact h_assumptions

def circuit : GeneralFormalCircuit (F p) field unit :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.EnforceZero
