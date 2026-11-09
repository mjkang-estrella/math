import Recurrence

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem cosh_product_identity (v u : ℝ) :
    Real.cosh u * Real.cosh (v * u) =
      (Real.cosh ((v + 1) * u) + Real.cosh ((v - 1) * u)) / 2 := by
  rw [add_mul, sub_mul, one_mul, Real.cosh_add, Real.cosh_sub]
  ring

theorem besselIntegrand_cosh_identity (v x u : ℝ) :
    Real.cosh u * besselIntegrand v x u =
      (besselIntegrand (v + 1) x u + besselIntegrand (v - 1) x u) / 2 := by
  unfold besselIntegrand
  have h := cosh_product_identity v u
  linear_combination Real.exp (-x * Real.cosh u) * h

theorem cosh_besselIntegrand_integrable (v : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u => Real.cosh u * besselIntegrand v x u) := by
  simp_rw [besselIntegrand_cosh_identity]
  exact ((besselIntegrand_integrable (v + 1) hx).add
    (besselIntegrand_integrable (v - 1) hx)).div_const 2

theorem besselIntegrand_argument_hasDerivAt (v x u : ℝ) :
    HasDerivAt (fun t => besselIntegrand v t u)
      (-Real.cosh u * besselIntegrand v x u) x := by
  have h := ((((hasDerivAt_id x).neg).mul_const (Real.cosh u)).exp).mul_const
    (Real.cosh (v * u))
  convert! h using 1
  simp only [besselIntegrand, Pi.neg_apply, id_eq, neg_mul, one_mul]
  ring

theorem besselK_hasDerivAt {x : ℝ} (hx : 0 < x) (v : ℝ) :
    HasDerivAt (besselK v)
      (-(besselK (v + 1) x + besselK (v - 1) x) / 2) x := by
  let B : ℝ → ℝ := fun u => Real.cosh u * besselIntegrand v (x / 2) u
  have hB : IntegrableOn B (Ioi 0) :=
    (cosh_besselIntegrand_integrable v (by linarith : 0 < x / 2)).integrableOn
  have hF : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (besselIntegrand v y)
      (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with y
    exact (show Continuous (besselIntegrand v y) by unfold besselIntegrand; fun_prop).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (fun u => -Real.cosh u * besselIntegrand v x u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (show Continuous (fun u => -Real.cosh u * besselIntegrand v x u) by
      unfold besselIntegrand; fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ y ∈ Ioi (x / 2),
      ‖-Real.cosh u * besselIntegrand v y u‖ ≤ B u := by
    filter_upwards [] with u y hy
    have hcy : Real.exp (-y * Real.cosh u) ≤ Real.exp (-(x / 2) * Real.cosh u) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right hy.le (Real.cosh_pos u).le)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_pos (Real.cosh_pos u), abs_of_nonneg (by unfold besselIntegrand; positivity)]
    unfold B besselIntegrand
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcy (Real.cosh_pos _).le) (Real.cosh_pos _).le
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y u => besselIntegrand v y u)
    (F' := fun y u => -Real.cosh u * besselIntegrand v y u)
    (Ioi_mem_nhds (by linarith : x / 2 < x)) hF
    (besselIntegrand_integrable v hx).integrableOn hF' hbound hB
    (by filter_upwards [] with u y _; exact besselIntegrand_argument_hasDerivAt v y u)
  have hp := (besselIntegrand_integrable (v + 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have hm := (besselIntegrand_integrable (v - 1) hx).integrableOn (s := Ioi (0 : ℝ))
  have heq : (∫ u in Ioi (0 : ℝ), -Real.cosh u * besselIntegrand v x u) =
      -(besselK (v + 1) x + besselK (v - 1) x) / 2 := by
    simp_rw [neg_mul, besselIntegrand_cosh_identity]
    rw [integral_neg, integral_div, integral_add hp hm]
    simp only [besselK, neg_div]
  rw [heq] at hd
  exact hd.2

theorem besselK_hasDerivAt_lower {x : ℝ} (hx : 0 < x) (v : ℝ) :
    HasDerivAt (besselK v) (-besselK (v - 1) x - v / x * besselK v x) x := by
  convert! besselK_hasDerivAt hx v using 1
  have h := besselK_recurrence hx v
  have heq : 2 * v / x * besselK v x = 2 * (v / x * besselK v x) := by ring
  rw [heq] at h
  linarith

end GauntIntegral
