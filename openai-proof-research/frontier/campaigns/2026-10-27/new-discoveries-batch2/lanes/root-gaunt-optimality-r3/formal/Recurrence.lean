import IntegralBase

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem abs_sinh_le_cosh (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  apply abs_le.mpr
  constructor
  · have h := Real.sinh_lt_cosh (-u)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (Real.sinh_lt_cosh u).le

theorem sinh_boundary_norm_bound (v : ℝ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖Real.exp (-x * Real.cosh u) * Real.sinh (v * u)‖ ≤
      Real.exp (|v| ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (abs_sinh_le_cosh (v * u))
    (Real.exp_pos _).le).trans (besselIntegrand_gaussian_bound v hx u)

theorem sinh_boundary_tendsto (v : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.sinh (v * u))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (sinh_boundary_norm_bound v hx)
  have h := Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
      (by linarith : -(x / 4) < 0))
  simpa only [mul_zero, Function.comp_apply] using h.const_mul (Real.exp (|v| ^ 2 / x))

theorem cosh_difference_identity (v u : ℝ) :
    Real.cosh ((v + 1) * u) - Real.cosh ((v - 1) * u) =
      2 * Real.sinh (v * u) * Real.sinh u := by
  rw [add_mul, sub_mul, one_mul, Real.cosh_add, Real.cosh_sub]
  ring

theorem sinh_boundary_hasDerivAt (v x u : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-x * Real.cosh t) * Real.sinh (v * t))
      (v * besselIntegrand v x u - x / 2 *
        (besselIntegrand (v + 1) x u - besselIntegrand (v - 1) x u)) u := by
  have h := (((Real.hasDerivAt_cosh u).const_mul (-x)).exp).mul
    ((Real.hasDerivAt_sinh (v * u)).comp u ((hasDerivAt_id u).const_mul v))
  convert! h using 1
  dsimp [besselIntegrand]
  have hc := cosh_difference_identity v u
  linear_combination (-x * Real.exp (-x * Real.cosh u) / 2) * hc

theorem besselK_recurrence {x : ℝ} (hx : 0 < x) (v : ℝ) :
    besselK (v + 1) x - besselK (v - 1) x = (2 * v / x) * besselK v x := by
  have hv := (besselIntegrand_integrable v hx).integrableOn (s := Ioi (0 : ℝ))
  have hp := (besselIntegrand_integrable (v + 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have hm := (besselIntegrand_integrable (v - 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => sinh_boundary_hasDerivAt v x u)
    ((hv.const_mul v).sub ((hp.sub hm).const_mul (x / 2))) (sinh_boundary_tendsto v hx)
  simp only [mul_zero, Real.sinh_zero, mul_zero, sub_zero] at hi
  have hsub := integral_sub (hv.const_mul v) ((hp.sub hm).const_mul (x / 2))
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_const_mul, integral_const_mul] at hi
  have hdiff := integral_sub hp hm
  rw [hdiff] at hi
  change v * besselK v x - x / 2 * (besselK (v + 1) x - besselK (v - 1) x) = 0 at hi
  apply (mul_left_inj' (ne_of_gt hx)).mp
  field_simp
  nlinarith

end GauntIntegral
