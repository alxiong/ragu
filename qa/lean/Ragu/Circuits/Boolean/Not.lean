import Clean.Circuit

namespace Ragu.Circuits.Boolean.Not
variable {p : ℕ} [Fact p.Prime]

/-- `Boolean::not` is free in the circuit model: it emits no gates or
constraints and simply returns a new `Boolean` whose wire is the virtual
expression `1 - self.wire()`. -/
def main (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  return 1 - input

/-- The caller must promise the input is boolean; otherwise the output is
not meaningfully a boolean negation. -/
def Assumptions (input : F p) := input = 0 ∨ input = 1

/-- The output equals `1 - input`. Stated independently of `Assumptions`
so soundness is non-tautological. -/
def Spec (input : F p) (output : F p) := output = 1 - input

instance elaborated : ElaboratedCircuit (F p) field field where
  main
  localLength _ := 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) field field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.Not
