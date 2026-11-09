import NormBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter

namespace MittagModulus

/-- Genuine Euler-product approximations to the Mittag-Leffler coefficients. -/
noncomputable def approxCoeff (a : ℝ) (n N : ℕ) : ℝ :=
  momentApprox (2 * a) ((n : ℝ) / 2) N / Real.Gamma (1 + (n : ℝ) / 2)

theorem approxCoeff_nonneg {a : ℝ} (ha : 0 ≤ a) (n N : ℕ) :
    0 ≤ approxCoeff a n N := by
  unfold approxCoeff
  exact div_nonneg (momentApprox_pos (by positivity) (by positivity) N).le
    (Real.Gamma_pos_of_pos (by positivity)).le

theorem approxCoeff_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (n N : ℕ) :
    approxCoeff a n N ≤ 1 / Real.Gamma (a * (n : ℝ) + 1) := by
  have hG : 0 < Real.Gamma (1 + (n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hH : 0 < Real.Gamma (a * (n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have h := momentApprox_le_gammaRatio (by positivity : 0 ≤ 2 * a)
    (by linarith : 2 * a ≤ 1) (by positivity : 0 ≤ (n : ℝ) / 2) N
  have he : 1 + (2 * a) * ((n : ℝ) / 2) = a * (n : ℝ) + 1 := by ring
  rw [he] at h
  unfold approxCoeff
  apply (div_le_iff₀ hG).mpr
  simpa only [one_div_mul_eq_div] using h

theorem approxCoeff_tendsto {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Tendsto (approxCoeff a n) atTop (nhds (1 / Real.Gamma (a * (n : ℝ) + 1))) := by
  have hG : Real.Gamma (1 + (n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hH : Real.Gamma (a * (n : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have h := (momentApprox_tendsto (by positivity : 0 ≤ 2 * a)
    (by positivity : 0 ≤ (n : ℝ) / 2)).div_const (Real.Gamma (1 + (n : ℝ) / 2))
  have he : 1 + 2 * a * ((n : ℝ) / 2) = a * (n : ℝ) + 1 := by ring
  rw [he] at h
  have heq : Real.Gamma (1 + (n : ℝ) / 2) / Real.Gamma (a * (n : ℝ) + 1) /
      Real.Gamma (1 + (n : ℝ) / 2) = 1 / Real.Gamma (a * (n : ℝ) + 1) := by
    field_simp
  rw [heq] at h
  exact h

noncomputable def approxTransform (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (approxCoeff a n N : ℂ) * z ^ n

theorem approx_term_norm_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (N n : ℕ) (z : ℂ) :
    ‖(approxCoeff a n N : ℂ) * z ^ n‖ ≤ ‖z‖ ^ n / Real.Gamma (a * (n : ℝ) + 1) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (approxCoeff_nonneg ha n N)]
  calc
    approxCoeff a n N * ‖z‖ ^ n ≤ (1 / Real.Gamma (a * (n : ℝ) + 1)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (approxCoeff_le ha ha2 n N) (by positivity)
    _ = ‖z‖ ^ n / Real.Gamma (a * (n : ℝ) + 1) := by ring

theorem approxTransform_summable {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (N : ℕ) (z : ℂ) : Summable (fun n : ℕ => (approxCoeff a n N : ℂ) * z ^ n) :=
  (mittag_real_majorant_summable ha zero_lt_one (norm_nonneg z)).of_norm_bounded
    (fun n => approx_term_norm_le ha.le ha2 N n z)

theorem approxTransform_tendsto {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (z : ℂ) :
    Tendsto (fun N : ℕ => approxTransform a N z) atTop (nhds (mittagLeffler a 1 z)) := by
  unfold approxTransform mittagLeffler
  apply tendsto_tsum_of_dominated_convergence
    (mittag_real_majorant_summable ha zero_lt_one (norm_nonneg z))
  · intro n
    have h := (Complex.continuous_ofReal.tendsto _).comp (approxCoeff_tendsto ha.le n)
    simpa only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_one,
      one_div_mul_eq_div] using h.mul_const (z ^ n)
  · exact Eventually.of_forall (fun N n => approx_term_norm_le ha.le ha2 N n z)

end MittagModulus
