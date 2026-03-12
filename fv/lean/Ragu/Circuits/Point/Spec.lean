import Clean.Circuit
import Clean.Utils.Primes

namespace Ragu.Circuits.Point.Spec
variable {p : ℕ} [Fact p.Prime]

structure Point (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
  NOTE: supports only short Weirstrass curves with a = 0
  TODO: replace with Weirstrass in Mathlib
-/
structure CurveParams (F : Type) where
  b : F

def Point.isOnCurve (point : Point (F p)) (curveParams : CurveParams (F p)) : Prop :=
  point.y^2 = point.x^3 + curveParams.b

def Point.double (point : Point (F p)) : Point (F p) :=
  let lambda := (3 * point.x^2) / (2 * point.y)
  let x2 := lambda^2 - 2*point.x
  {
    x := x2,
    y := lambda * (point.x - x2) - point.y
  }

end Ragu.Circuits.Point.Spec
