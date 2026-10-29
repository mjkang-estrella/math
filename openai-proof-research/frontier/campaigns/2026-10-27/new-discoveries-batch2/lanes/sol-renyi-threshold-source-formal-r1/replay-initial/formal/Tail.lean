module
public import Pointwise
public import Majorant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public section
set_option autoImplicit false
set_option warningAsError true
open Real Filter MeasureTheory Set
open scoped Topology
namespace Renyi
@[expose] noncomputable def tail (p a : ℝ) : ℝ :=
  ∫ u in Ioi (0:ℝ), exp (-p*u) * bracket p a u

theorem tail_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (tail p) atTop (𝓝 0) := by
  have hp0 : 0 ≤ p := hp.le
  have hc (a : ℝ) : Continuous (fun u : ℝ => exp (-p*u) * bracket p a u) := by
    unfold bracket
    fun_prop
  have H := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun a u : ℝ => exp (-p*u) * bracket p a u) (f := fun _ => (0:ℝ))
    (fun u : ℝ => exp (-p*u) * (2*u)^p)
    (Filter.Eventually.of_forall (fun a => (hc a).aestronglyMeasurable))
    (show ∀ᶠ a : ℝ in atTop, ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)),
      ‖exp (-p*u) * bracket p a u‖ ≤ exp (-p*u) * (2*u)^p from by
      filter_upwards [eventually_ge_atTop 0] with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hb := bracket_bounds hp hp1 ha (le_of_lt hu)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le hb.1)]
      exact mul_le_mul_of_nonneg_left hb.2 (exp_pos _).le)
    (majorant_integrable hp)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa using (bracket_tendsto hp hp1 (le_of_lt hu)).const_mul (exp (-p*u)))
  change Tendsto (fun a : ℝ => ∫ u in Ioi (0:ℝ), exp (-p*u) * bracket p a u)
    atTop (𝓝 0)
  simpa only [integral_zero] using H

theorem tail_integrable {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => exp (-p*u)*bracket p a u) (Ioi 0) := by
  have hp0 : 0 ≤ p := hp.le
  apply (majorant_integrable hp).mono'
  · apply Continuous.aestronglyMeasurable
    unfold bracket
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hb := bracket_bounds hp hp1 ha (le_of_lt hu)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 (exp_pos _).le

@[expose] noncomputable def J (p : ℝ) : ℝ :=
  ∫ u in Ioi (0:ℝ), exp (-p*u)*u^p

theorem J_pos {p : ℝ} (hp : 0 < p) : 0 < J p := by
  apply (integral_pos_iff_support_of_nonneg_ae _ (moment_integrable hp)).mpr
  · have hs : (Ioi (0:ℝ)) ⊆ Function.support (fun u : ℝ => exp (-p*u)*u^p) := by
      intro u hu
      exact (mul_pos (exp_pos _) (rpow_pos_of_pos hu p)).ne'
    have hm := measure_mono (μ := volume.restrict (Ioi (0:ℝ))) hs
    rw [Measure.restrict_apply measurableSet_Ioi] at hm
    simpa using (lt_of_lt_of_le (by simp : 0 < volume (Ioi (0:ℝ) ∩ Ioi 0)) hm)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos (exp_pos _) (rpow_pos_of_pos hu p)).le

theorem eventually_tail_lt_J {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∀ᶠ a : ℝ in atTop, tail p a < J p :=
  (tail_tendsto hp hp1).eventually (gt_mem_nhds (J_pos hp))

end Renyi
