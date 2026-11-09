import Mathlib

namespace MatkowskiCounterexample

def Equation (f : ℝ → ℝ) : Prop :=
  ∀ x, f (f (-x) + x) = f (-f x) + f x

def cap (x : ℝ) : ℝ := min (max x 0) 1

theorem cap_continuous : Continuous cap := by
  exact (continuous_id.max continuous_const).min continuous_const

theorem cap_nonneg (x : ℝ) : 0 ≤ cap x := by
  exact le_min (le_max_right _ _) (by norm_num)

theorem cap_of_nonpos {x : ℝ} (hx : x ≤ 0) : cap x = 0 := by
  simp [cap, max_eq_right hx]

theorem cap_le_self {x : ℝ} (hx : 0 ≤ x) : cap x ≤ x := by
  simp only [cap, max_eq_left hx]
  exact min_le_left _ _

theorem cap_equation : Equation cap := by
  intro x
  have hzero : cap 0 = 0 := cap_of_nonpos le_rfl
  have hneg : cap (-cap x) = 0 := cap_of_nonpos (neg_nonpos.mpr (cap_nonneg x))
  rw [hneg, zero_add]
  by_cases hx : 0 ≤ x
  · rw [cap_of_nonpos (neg_nonpos.mpr hx), zero_add]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [cap_of_nonpos hx']
    apply cap_of_nonpos
    have h := cap_le_self (neg_nonneg.mpr hx')
    linarith

theorem cap_one : cap 1 = 1 := by norm_num [cap]

theorem cap_two : cap 2 = 1 := by norm_num [cap]

theorem cap_not_linear_on_positive : ¬ ∃ b : ℝ, ∀ x : ℝ, 0 < x → cap x = b * x := by
  rintro ⟨b, hb⟩
  have h1 := hb 1 (by norm_num)
  have h2 := hb 2 (by norm_num)
  rw [cap_one] at h1
  rw [cap_two] at h2
  linarith

theorem cap_not_two_slopes : ¬ ∃ a b : ℝ,
    ∀ x : ℝ, cap x = if x ≤ 0 then a*x else b*x := by
  rintro ⟨a, b, h⟩
  apply cap_not_linear_on_positive
  refine ⟨b, ?_⟩
  intro x hx
  simpa [not_le.mpr hx] using h x

theorem continuous_nonlinear_counterexample :
    ∃ f : ℝ → ℝ, Continuous f ∧ Equation f ∧
      ¬ ∃ a b : ℝ, ∀ x : ℝ, f x = if x ≤ 0 then a*x else b*x := by
  exact ⟨cap, cap_continuous, cap_equation, cap_not_two_slopes⟩

end MatkowskiCounterexample
