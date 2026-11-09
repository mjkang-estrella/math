import GammaAsymptotic

namespace Schmidlin

theorem gammaError_unit_bounds {n : ℕ} (hn : 2 ≤ n) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    gammaError n - 2/((n:ℝ)-1) ≤ gammaError ((n:ℝ)+r) ∧
    gammaError ((n:ℝ)+r) ≤ gammaError n + 1/(n:ℝ) := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hnm : 0 < (n:ℝ)-1 := by linarith
  rcases eq_or_lt_of_le hr0 with heq | hr
  · subst r
    constructor <;> simp only [add_zero] <;> linarith [show (0:ℝ) < 2/((n:ℝ)-1) by positivity,
      show (0:ℝ) < 1/(n:ℝ) by positivity]
  have hnr : 0 < (n:ℝ)+r := by linarith
  have hA : 0 < (n:ℝ)+r-1/2 := by linarith
  have hu := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma
    (fun {_} h => logGamma_add_one h) (by omega : n ≠ 0) hr hr1
  have hl := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma
    (fun {_} h => logGamma_add_one h) hn hr
  simp only [Function.comp_def] at hu hl
  have he : Real.log ((n:ℝ)+r) = Real.log (n:ℝ)+Real.log (((n:ℝ)+r)/n) := by
    rw [Real.log_div (ne_of_gt hnr) (ne_of_gt hn0)]
    ring
  have hrlo := Real.one_sub_inv_le_log_of_pos (div_pos hnr hn0)
  have hrhi := Real.log_le_sub_one_of_pos (div_pos hnr hn0)
  have hlo : r/((n:ℝ)+r) ≤ Real.log (((n:ℝ)+r)/n) := by
    convert hrlo using 1
    field_simp
    ring
  have hhi : Real.log (((n:ℝ)+r)/n) ≤ r/(n:ℝ) := by
    convert hrhi using 1
    field_simp
    ring
  have hm := Real.one_sub_inv_le_log_of_pos (div_pos hnm hn0)
  have hmlog : Real.log ((n:ℝ)-1) ≥ Real.log (n:ℝ)-1/((n:ℝ)-1) := by
    rw [Real.log_div (ne_of_gt hnm) (ne_of_gt hn0)] at hm
    have hrat : 1-(((n:ℝ)-1)/n)⁻¹ = -1/((n:ℝ)-1) := by field_simp; ring
    rw [hrat] at hm
    simp only [neg_div] at hm
    linarith
  have hmullo := mul_le_mul_of_nonneg_left hlo hA.le
  have hmulhi := mul_le_mul_of_nonneg_left hhi hA.le
  have hml := mul_le_mul_of_nonneg_left hmlog hr0
  have hupper : r-((n:ℝ)+r-1/2)*(r/((n:ℝ)+r)) ≤ 1/(n:ℝ) := by
    apply (le_div_iff₀ hn0).2
    field_simp
    nlinarith [mul_nonneg hr0 hn0.le]
  have hlower : -2/((n:ℝ)-1) ≤
      r-r/((n:ℝ)-1)-((n:ℝ)+r-1/2)*(r/(n:ℝ)) := by
    apply (div_le_iff₀ hnm).2
    field_simp
    have hprod := mul_nonneg (sub_nonneg.mpr hr1) hn0.le
    have hprod2 := mul_nonneg (show 0 ≤ r-r*r by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]) hnm.le
    nlinarith [sq_nonneg r]
  unfold gammaError
  rw [he]
  simp only [div_eq_mul_inv] at *
  constructor <;> nlinarith

end Schmidlin
