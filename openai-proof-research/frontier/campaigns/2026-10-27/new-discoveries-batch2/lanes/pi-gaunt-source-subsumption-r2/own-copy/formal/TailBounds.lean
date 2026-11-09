import ArgumentDerivative

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

def weightedK (v m x : ℝ) : ℝ := x ^ (-v) * besselK m x

theorem besselK_nonneg (m x : ℝ) : 0 ≤ besselK m x := by
  apply integral_nonneg
  intro u
  unfold besselIntegrand
  positivity

theorem besselK_exponential_bound (m : ℝ) {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    besselK m x ≤ Real.exp (-(1 / 2 : ℝ) * x) * besselK m (a / 2) := by
  have hx : 0 < x := ha.trans_le hax
  have hi := (besselIntegrand_integrable m hx).integrableOn (s := Ioi (0 : ℝ))
  have hj := ((besselIntegrand_integrable m (by linarith : 0 < a / 2)).integrableOn
    (s := Ioi (0 : ℝ))).const_mul (Real.exp (-(1 / 2 : ℝ) * x))
  have hp : ∀ u : ℝ, besselIntegrand m x u ≤
      Real.exp (-(1 / 2 : ℝ) * x) * besselIntegrand m (a / 2) u := by
    intro u
    have he : -x * Real.cosh u ≤ -(1 / 2 : ℝ) * x - a / 2 * Real.cosh u := by
      have hc := Real.one_le_cosh u
      nlinarith [mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hc)]
    unfold besselIntegrand
    calc
      _ ≤ Real.exp (-(1 / 2 : ℝ) * x - a / 2 * Real.cosh u) * Real.cosh (m * u) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (Real.cosh_pos _).le
      _ = _ := by
        rw [show -(1 / 2 : ℝ) * x - a / 2 * Real.cosh u =
          -(1 / 2 : ℝ) * x + (-(a / 2) * Real.cosh u) by ring, Real.exp_add]
        ring
  have h := integral_mono_ae hi hj (Filter.Eventually.of_forall hp)
  rw [integral_const_mul] at h
  exact h

theorem weightedK_exponential_bound {v a x : ℝ} (hv : 0 ≤ v) (ha : 0 < a)
    (hax : a ≤ x) (m : ℝ) :
    ‖weightedK v m x‖ ≤
      (a ^ (-v) * besselK m (a / 2)) * Real.exp (-(1 / 2 : ℝ) * x) := by
  have hx := ha.trans_le hax
  have hr := Real.rpow_le_rpow_of_nonpos ha hax (neg_nonpos.mpr hv)
  have hk := besselK_exponential_bound m ha hax
  rw [weightedK, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (besselK_nonneg _ _))]
  calc
    x ^ (-v) * besselK m x ≤ a ^ (-v) *
        (Real.exp (-(1 / 2 : ℝ) * x) * besselK m (a / 2)) :=
      mul_le_mul hr hk (besselK_nonneg _ _) (Real.rpow_nonneg ha.le _)
    _ = _ := by ring

theorem weightedK_continuousOn (v m : ℝ) : ContinuousOn (weightedK v m) (Ioi 0) := by
  intro x hx
  exact (((Real.hasDerivAt_rpow_const (p := -v) (Or.inl (ne_of_gt hx))).mul
    (besselK_hasDerivAt hx m)).continuousAt).continuousWithinAt

theorem weightedK_integrableOn {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) (m : ℝ) :
    IntegrableOn (weightedK v m) (Ioi a) := by
  have hg := (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) a).const_mul
    (a ^ (-v) * besselK m (a / 2))
  have hc := (weightedK_continuousOn v m).mono (show Ioi a ⊆ Ioi 0 by
    intro x hx; exact ha.trans hx)
  apply hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact weightedK_exponential_bound hv ha hx.le m

theorem weightedK_tendsto_zero {v : ℝ} (hv : 0 ≤ v) (m : ℝ) :
    Tendsto (weightedK v m) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  apply squeeze_zero_norm' (a := fun x : ℝ =>
    ((1 : ℝ) ^ (-v) * besselK m (1 / 2)) * Real.exp (-(1 / 2 : ℝ) * x))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact weightedK_exponential_bound hv (by norm_num : (0 : ℝ) < 1) hx m
  · simpa only [Function.comp_apply, mul_zero, id_eq] using
      he.const_mul ((1 : ℝ) ^ (-v) * besselK m (1 / 2))

end GauntIntegral
