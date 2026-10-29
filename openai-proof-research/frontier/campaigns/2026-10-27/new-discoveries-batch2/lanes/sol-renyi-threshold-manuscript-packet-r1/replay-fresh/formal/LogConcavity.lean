module
public import Density
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
-- The open-weight formulation includes all nontrivial weights; weights 0 and 1
-- give equality without imposing a convention for 0^0.
@[expose] def LogConcaveDensity (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ x y t : ℝ, 0 < t → t < 1 →
    (f x)^t * (f y)^(1-t) ≤ f (t*x+(1-t)*y)

theorem density_logConcave {a : ℝ} (ha : 0 < a) : LogConcaveDensity (density a) := by
  refine ⟨density_nonneg ha, ?_⟩
  intro x y t ht ht1
  have ht' : 0 < 1-t := sub_pos.mpr ht1
  by_cases hx : x ∈ Icc 0 a
  · by_cases hy : y ∈ Icc 0 a
    · have hz : t*x+(1-t)*y ∈ Icc 0 a := by
        constructor
        · exact add_nonneg (mul_nonneg ht.le hx.1) (mul_nonneg ht'.le hy.1)
        · have H1 := mul_le_mul_of_nonneg_left hx.2 ht.le
          have H2 := mul_le_mul_of_nonneg_left hy.2 ht'.le
          nlinarith
      simp only [density, indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz]
      rw [mul_rpow (normalizer_pos ha).le (exp_pos _).le,
        mul_rpow (normalizer_pos ha).le (exp_pos _).le]
      have he : normalizer a ^ t * normalizer a ^ (1-t) = normalizer a := by
        rw [← rpow_add (normalizer_pos ha), add_sub_cancel, rpow_one]
      rw [← exp_mul, ← exp_mul]
      have hid : (normalizer a ^ t * exp (-x*t)) *
          (normalizer a ^ (1-t) * exp (-y*(1-t))) =
          (normalizer a ^ t * normalizer a ^ (1-t)) *
            (exp (-x*t)*exp (-y*(1-t))) := by ring
      rw [hid, he, ← exp_add]
      have harg : -x*t + -y*(1-t) = -(t*x+(1-t)*y) := by ring
      rw [harg]
    · rw [show density a y=0 by simp [density,hy], zero_rpow ht'.ne', mul_zero]
      exact density_nonneg ha _
  · rw [show density a x=0 by simp [density,hx], zero_rpow ht.ne', zero_mul]
    exact density_nonneg ha _
end Renyi
