import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
noncomputable def d : ℝ := Real.sqrt 17
noncomputable def A (t : ℝ) : ℝ :=
  (Real.cosh (4*t) - Real.cosh t * Real.cosh (d*t) +
    (5/d)*Real.sinh t * Real.sinh (d*t))/2
noncomputable def B (t : ℝ) : ℝ :=
  Real.sinh t * (Real.cosh (5*t) - Real.cosh (d*t))/2
noncomputable def U (t : ℝ) : ℝ := deriv B t * A t - B t * deriv A t - A t ^ 2
noncomputable def V (t : ℝ) : ℝ := -4 * B t * A t
noncomputable def E (t : ℝ) : ℝ := (1+2*t^2)*U t + t*V t
theorem d_sq : d^2 = 17 := Real.sq_sqrt (by norm_num)
theorem d_nonneg : 0 ≤ d := Real.sqrt_nonneg _
theorem d_bounds : (41:ℝ)/10 < d ∧ d < (21:ℝ)/5 := by
  have h := d_sq
  have h0 := d_nonneg
  constructor <;> nlinarith
theorem d_ne : d ≠ 0 := ne_of_gt (lt_trans (by norm_num) d_bounds.1)
end LogArctangentMean
