import KernelEventual

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

def tailDefectIntegrand (v m r t : ℝ) : ℝ := weightedK v m t -
  (weightedK v (r - 1) t + (v + r) * weightedK (v + 1) r t)

theorem tailDefectIntegrand_integrable {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) (m r : ℝ) :
    IntegrableOn (tailDefectIntegrand v m r) (Ioi a) := by
  exact (weightedK_integrableOn hv ha m).sub
    ((weightedK_integrableOn hv ha (r - 1)).add
      ((weightedK_integrableOn (by linarith : 0 ≤ v + 1) ha r).const_mul (v + r)))

theorem tailDefectIntegrand_eq {x : ℝ} (hx : 0 < x) (v m r : ℝ) :
    tailDefectIntegrand v m r x = x ^ (-v) * comparisonBessel v m r x := by
  unfold tailDefectIntegrand weightedK comparisonBessel
  rw [show -(v + 1) = -v - 1 by ring, Real.rpow_sub hx, Real.rpow_one]
  ring

theorem tailDefectIntegrand_integral {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) (m r : ℝ) :
    (∫ t in Ioi a, tailDefectIntegrand v m r t) =
      (∫ t in Ioi a, weightedK v m t) - weightedK v r a := by
  have hm := weightedK_integrableOn hv ha m
  have hp := (weightedK_integrableOn hv ha (r - 1)).add
    ((weightedK_integrableOn (by linarith : 0 ≤ v + 1) ha r).const_mul (v + r))
  have hi := weightedK_derivative_integral hv ha r
  rw [integral_neg] at hi
  have heq := neg_injective hi
  have hsub := integral_sub hm hp
  simp only [Pi.add_apply] at hsub
  change (∫ t in Ioi a, weightedK v m t -
    (weightedK v (r - 1) t + (v + r) * weightedK (v + 1) r t)) = _
  rw [hsub, heq]

theorem integral_Ioi_negative {a : ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi a))
    (hneg : ∀ t ∈ Ioi a, f t < 0) : (∫ t in Ioi a, f t) < 0 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi a)] (fun t => -f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (neg_pos.mpr (hneg t ht)).le
  have hsub : Ioo (a + 1) (a + 2) ⊆ Function.support (fun t => -f t) ∩ Ioi a := by
    intro t ht
    have hta : a < t := by linarith [ht.1]
    exact ⟨ne_of_gt (neg_pos.mpr (hneg t hta)), hta⟩
  have hp := (setIntegral_pos_iff_support_of_nonneg_ae hn hf.neg).2
    (lt_of_lt_of_le (by simp only [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith))
      (measure_mono hsub))
  rw [integral_neg] at hp
  exact neg_pos.mp hp

theorem tail_eventually_below_larger_order {d v m r : ℝ} (hd : 0 ≤ d) (hdv : d < v)
    (hdr : d < r) (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧
      (∫ t in Ioi x, weightedK v m t) < weightedK v r x := by
  have hv : 0 ≤ v := hd.trans hdv.le
  obtain ⟨R, hR⟩ := eventually_atTop.mp (comparisonBessel_eventually_negative hd hdr hm)
  filter_upwards [eventually_ge_atTop (max R 1)] with x hx
  have hxR : R ≤ x := (le_max_left R 1).trans hx
  have hx1 : 1 ≤ x := (le_max_right R 1).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1
  refine ⟨hx0, ?_⟩
  have hneg : ∀ t ∈ Ioi x, tailDefectIntegrand v m r t < 0 := by
    intro t ht
    have ht0 := hx0.trans ht
    rw [tailDefectIntegrand_eq ht0]
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos ht0 (-v)) (hR t (hxR.trans ht.le))
  have hi := integral_Ioi_negative (tailDefectIntegrand_integrable hv hx0 m r) hneg
  rw [tailDefectIntegrand_integral hv hx0 m r] at hi
  exact sub_neg.mp hi

end GauntIntegral
