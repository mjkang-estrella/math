import LocalSign

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem laplace_eventually_negative {h : ℝ → ℝ} {a b e c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbe : b < e) (hc : 0 < c)
    (hnear : ∀ u ∈ Ioc (0 : ℝ) e, h u ≤ 0)
    (hwindow : ∀ u ∈ Icc a b, h u ≤ -c)
    (hint : ∀ x : ℝ, 0 < x → IntegrableOn (fun u => Real.exp (-x * Real.cosh u) * h u) (Ioi 0)) :
    ∀ᶠ x : ℝ in atTop, (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * h u) < 0 := by
  let g : ℝ → ℝ := fun u => Real.exp (-Real.cosh u) * |h u|
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul] using!
      (hint 1 (by norm_num)).norm
  let C : ℝ := ∫ u in Ioi (0 : ℝ), g u
  have hC : 0 ≤ C := integral_nonneg (fun u => by dsimp [g]; positivity)
  have hcos : Real.cosh b < Real.cosh e := by
    apply Real.cosh_lt_cosh.mpr
    rw [abs_of_pos (ha.trans hab), abs_of_pos ((ha.trans hab).trans hbe)]
    exact hbe
  have hgap : 0 < Real.cosh e - Real.cosh b := sub_pos.mpr hcos
  have hlimit : Tendsto
      (fun x : ℝ => C * Real.exp (Real.cosh e) *
        Real.exp (-(Real.cosh e - Real.cosh b) * x)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap))
    simpa only [Function.comp_apply, id_eq, mul_zero] using he.const_mul (C * Real.exp (Real.cosh e))
  have hevent := hlimit.eventually (gt_mem_nhds (mul_pos hc (sub_pos.mpr hab)))
  filter_upwards [hevent, eventually_ge_atTop (1 : ℝ)] with x hxsmall hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  let q : ℝ → ℝ := (Icc a b).indicator (fun _ => -c * Real.exp (-x * Real.cosh b))
  let T : ℝ := Real.exp (-(x - 1) * Real.cosh e)
  have hq : IntegrableOn q (Ioi 0) := by
    exact ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (s := Icc a b) (C := -c * Real.exp (-x * Real.cosh b))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).integrableOn
  have hT : 0 ≤ T := (Real.exp_pos _).le
  have hpoint : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * h u ≤ q u + T * g u := by
    intro u hu
    by_cases huw : u ∈ Icc a b
    · have hub : Real.cosh u ≤ Real.cosh b := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_pos hu, abs_of_pos (ha.trans hab)]
        exact huw.2
      have he : Real.exp (-x * Real.cosh b) ≤ Real.exp (-x * Real.cosh u) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hg0 : 0 ≤ T * g u := by dsimp [g, T]; positivity
      have hqeq : q u = -c * Real.exp (-x * Real.cosh b) :=
        Set.indicator_of_mem huw _
      rw [hqeq]
      have h1 := mul_le_mul_of_nonneg_left (hwindow u huw) (Real.exp_pos (-x * Real.cosh u)).le
      have h2 := mul_le_mul_of_nonpos_right he (neg_nonpos.mpr hc.le)
      nlinarith
    · have hqeq : q u = 0 := Set.indicator_of_notMem huw _
      rw [hqeq, zero_add]
      by_cases hue : u ≤ e
      · have h1 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-x * Real.cosh u)).le
          (hnear u ⟨hu, hue⟩)
        have h2 : 0 ≤ T * g u := by dsimp [T, g]; positivity
        exact h1.trans h2
      · have he : e ≤ u := (not_le.mp hue).le
        have he0 : 0 < e := (ha.trans hab).trans hbe
        have hcosu : Real.cosh e ≤ Real.cosh u := by
          apply Real.cosh_le_cosh.mpr
          rw [abs_of_pos he0, abs_of_pos hu]
          exact he
        have hbnd : Real.exp (-x * Real.cosh u) ≤ T * Real.exp (-Real.cosh u) := by
          dsimp [T]
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hcosu)]
        have h1 := mul_le_mul_of_nonneg_left (le_abs_self (h u)) (Real.exp_pos (-x * Real.cosh u)).le
        have h2 := mul_le_mul_of_nonneg_right hbnd (abs_nonneg (h u))
        dsimp [g]
        nlinarith
  have hupper := integral_mono_ae (hint x hx0) (hq.add (hg.const_mul T))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
  simp only [Pi.add_apply] at hupper
  rw [integral_add hq (hg.const_mul T), integral_const_mul] at hupper
  have hqi : (∫ u in Ioi (0 : ℝ), q u) = -(c * (b - a)) * Real.exp (-x * Real.cosh b) := by
    dsimp [q]
    rw [integral_indicator_const _ measurableSet_Icc,
      measureReal_restrict_apply measurableSet_Icc]
    have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun u hu => ha.trans_le hu.1
    rw [inter_eq_left.mpr hsub]
    simp only [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul]
    ring
  rw [hqi] at hupper
  change (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * h u) ≤
    -(c * (b - a)) * Real.exp (-x * Real.cosh b) + T * C at hupper
  have hTeq : T = Real.exp (-x * Real.cosh b) *
      (Real.exp (Real.cosh e) * Real.exp (-(Real.cosh e - Real.cosh b) * x)) := by
    dsimp [T]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall := mul_lt_mul_of_pos_left hxsmall (Real.exp_pos (-x * Real.cosh b))
  rw [hTeq] at hupper
  nlinarith

end GauntIntegral
