import Clean.Circuit
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.IsEqual
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Element::is_equal(other)` is `self.sub(other).is_zero()`. The trace
consists of the `is_zero` machinery (two gates, six wires, the standard
inverse trick) applied to the virtual difference `a - b`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x1, iz, zp⟩ ← (witness fun env =>
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    let diff := av - bv
    (⟨diff, (if diff = 0 then (1 : F p) else 0), 0⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x1 * iz - zp)
  assertZero (x1 - (input.a - input.b))
  assertZero zp
  let ⟨x2, inv, inz⟩ ← (witness fun env =>
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    let diff := av - bv
    (⟨diff, diff⁻¹, (if diff = 0 then (0 : F p) else 1)⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x2 * inv - inz)
  assertZero (x2 - (input.a - input.b))
  assertZero (inz - 1 + iz)
  return iz

def Assumptions (_input : Input (F p)) := True

/-- The output equals `1` when the two inputs are equal and `0` otherwise. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = if input.a = input.b then 1 else 0

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 6

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c4 c5
  -- c1 : x1 * iz = zp         c4 : x2 * inv = inz
  -- c2 : x1 = input_a + -input_b   c5 : x2 = input_a + -input_b
  -- c3 : zp = 0                    c6 : inz - 1 + iz = 0
  by_cases hab : input_a = input_b
  · -- Case a = b: the difference is 0, so iz must be 1.
    simp only [hab, if_true]
    have hdiff : input_a + -input_b = 0 := by rw [hab]; ring
    rw [c5, hdiff, zero_mul] at c4   -- c4 : 0 = env.get (i₀+5)
    linear_combination c4 + c6
  · -- Case a ≠ b: difference is nonzero, so iz must be 0.
    simp only [hab, if_false]
    have hdiff_ne : input_a + -input_b ≠ 0 := fun h => hab (add_neg_eq_zero.mp h)
    rw [c2, c3] at c1   -- c1 : (input_a + -input_b) * env.get (i₀+1) = 0
    rcases mul_eq_zero.mp c1 with hd | hiz
    · exact absurd hd hdiff_ne
    · exact hiz

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  obtain ⟨h_env1, h_env2⟩ := h_env
  have h0 := h_env1 (0 : Fin 3)
  have h1 := h_env1 (1 : Fin 3)
  have h2 := h_env1 (2 : Fin 3)
  have h3 := h_env2 (0 : Fin 3)
  have h4 := h_env2 (1 : Fin 3)
  have h5 := h_env2 (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum]
    at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  simp at h0 h1 h2 h3 h4 h5
  simp only [show ([1, 1, 1] : List ℕ).sum = 3 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gate 1 : x1 * iz - zp = 0
    rw [h0, h1, h2]
    split_ifs with hd
    · rw [hd]; ring
    · ring
  · -- x1 - (a - b) = 0
    rw [h0]; ring
  · -- zp = 0
    rw [h2]
  · -- gate 2 : x2 * inv - inz = 0
    rw [show i₀ + 3 + 1 + 1 = i₀ + 3 + 2 from by omega, h3, h4, h5]
    split_ifs with hd
    · rw [hd]; simp
    · rw [mul_inv_cancel₀ hd]; ring
  · -- x2 - (a - b) = 0
    rw [h3]; ring
  · -- inz - 1 + iz = 0
    rw [show i₀ + 3 + 1 + 1 = i₀ + 3 + 2 from by omega, h5, h1]
    split_ifs with hd <;> ring

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.IsEqual
