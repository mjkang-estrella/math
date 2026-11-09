import MeanAnalyticDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
theorem cosh_weight_pos (l t : ℝ) : 0 < Real.cosh (l*t) := Real.cosh_pos _
theorem cosh_weight_mono {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    Real.cosh (a*t) ≤ Real.cosh (b*t) := by
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg ha ht),
    abs_of_nonneg (mul_nonneg (le_trans ha hab) ht)]
  exact mul_le_mul_of_nonneg_right hab ht
theorem sinh_weight_nonneg {l t : ℝ} (hl : 0 ≤ l) (ht : 0 ≤ t) :
    0 ≤ l * Real.sinh (l*t) :=
  mul_nonneg hl (Real.sinh_nonneg_iff.mpr (mul_nonneg hl ht))
theorem sinh_weight_mono {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    a * Real.sinh (a*t) ≤ b * Real.sinh (b*t) :=
  mul_le_mul hab (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hab ht))
    (Real.sinh_nonneg_iff.mpr (mul_nonneg ha ht)) (le_trans ha hab)
theorem square_cosh_weight_nonneg (l t : ℝ) :
    0 ≤ l^2 * Real.cosh (l*t) :=
  mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))
theorem square_cosh_weight_mono {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (ht : 0 ≤ t) :
    a^2 * Real.cosh (a*t) ≤ b^2 * Real.cosh (b*t) := by
  exact mul_le_mul (by nlinarith) (cosh_weight_mono ha hab ht)
    (le_of_lt (Real.cosh_pos _)) (sq_nonneg _)
/-- A closed finite derivative ladder. Its hypotheses are genuine derivatives,
not a supplied sequence of moments. -/
theorem derivative_ladder (f : ℝ → ℝ) (N : ℕ)
    (hc : ∀ j ≤ N, Continuous (iteratedDeriv j f))
    (hj : ∀ j < N, 0 ≤ iteratedDeriv j f 0)
    (hN : ∀ t, 0 ≤ t → 0 < iteratedDeriv N f t) :
    ∀ t, 0 < t → 0 < f t := by
  have step : ∀ j ≤ N, ∀ t, 0 < t → 0 < iteratedDeriv j f t := by
    intro j hjN
    induction hjN using Nat.decreasingInduction with
    | self =>
      intro t ht
      exact hN t (le_of_lt ht)
    | of_succ j hjN ih =>
      have hm : StrictMonoOn (iteratedDeriv j f) (Set.Ici 0) :=
        strictMonoOn_of_deriv_pos (convex_Ici 0) (hc j (by omega)).continuousOn
          (by
            intro x hx
            rw [interior_Ici] at hx
            rw [← iteratedDeriv_succ]
            exact ih x hx)
      intro t ht
      exact lt_of_le_of_lt (hj j (by omega)) (hm (by simp) (le_of_lt ht) ht)
  simpa only [iteratedDeriv_zero] using step 0 (Nat.zero_le N)
end LogArctangentMean
