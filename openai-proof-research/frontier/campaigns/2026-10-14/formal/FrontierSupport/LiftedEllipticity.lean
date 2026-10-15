import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The zero-jet ellipticity calculation in I345, Section 7, after orthogonally
splitting the horizontal test vector parallel/perpendicular to `a`.
`y` is the squared norm of the perpendicular component, `x` the parallel
coordinate, `a` the length of the horizontal part of the unit lift direction,
`b` its vertical component, and `t = sqrt(e)`.

Only real polynomial identities and inequalities are certified here. This
does not formalize viscosity solutions, the coordinate reduction, Savin's
theorem, or the claimed p-uniform gradient estimate.
-/

namespace FrontierSupport.LiftedEllipticity

def form (a b t x s y : ℝ) : ℝ :=
  s^2 + y + x^2 + t^2 * s^2 - (a*x + b*t*s)^2

theorem square_decomposition (a b t x s y : ℝ)
    (hunit : a^2 + b^2 = 1) :
    form a b t x s y = y + (b*x - t*a*s)^2 + s^2 := by
  unfold form
  nlinarith [congrArg (fun z : ℝ => z * x^2) hunit,
    congrArg (fun z : ℝ => z * (t^2*s^2)) hunit]

theorem bounds (a b t x s y : ℝ)
    (hunit : a^2 + b^2 = 1) (ht : t^2 ≤ 1) (hy : 0 ≤ y) :
    b^2 / 3 * (y + x^2 + s^2) ≤ form a b t x s y ∧
    form a b t x s y ≤ 2 * (y + x^2 + s^2) := by
  rw [square_decomposition a b t x s y hunit]
  have ha : a^2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b^2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hat : 0 ≤ a^2 * (1-t^2) := mul_nonneg (sq_nonneg a) (by linarith)
  have hcoeff : 0 ≤ 3-b^2-2*t^2*a^2 := by nlinarith
  have hys : 0 ≤ (3-b^2)*y := mul_nonneg (by linarith) hy
  have hss : 0 ≤ (3-b^2-2*t^2*a^2)*s^2 :=
    mul_nonneg hcoeff (sq_nonneg s)
  have hlo : 0 ≤ (3-b^2)*y + (b*x-2*t*a*s)^2 +
      (b*x-t*a*s)^2 + (3-b^2-2*t^2*a^2)*s^2 :=
    add_nonneg (add_nonneg (add_nonneg hys (sq_nonneg _)) (sq_nonneg _)) hss
  have hrem : 0 ≤ a^2*(1-t^2)*(x^2+s^2) :=
    mul_nonneg hat (add_nonneg (sq_nonneg x) (sq_nonneg s))
  have hcs : (b*x-t*a*s)^2 ≤ x^2+s^2 := by
    nlinarith [sq_nonneg (b*s+t*a*x),
      congrArg (fun z : ℝ => z * (x^2+s^2)) hunit]
  constructor
  · nlinarith only [hlo]
  · nlinarith [sq_nonneg x]

theorem uniform_lower (a b t x s y b0 : ℝ)
    (hunit : a^2 + b^2 = 1) (ht : t^2 ≤ 1) (hy : 0 ≤ y)
    (hb0 : b0^2 ≤ b^2) :
    b0^2 / 3 * (y + x^2 + s^2) ≤ form a b t x s y := by
  have h := (bounds a b t x s y hunit ht hy).1
  have hn : 0 ≤ y + x^2 + s^2 :=
    add_nonneg (add_nonneg hy (sq_nonneg x)) (sq_nonneg s)
  have hm := mul_nonneg (sub_nonneg.mpr hb0) hn
  nlinarith

end FrontierSupport.LiftedEllipticity
