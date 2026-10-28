import ZeroOrder
import TailBounds

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace GauntIntegral

theorem besselK_differential_comparison {x d v m : ℝ} (hx : 0 < x)
    (hd : 0 ≤ d) (hdv : d < v) (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    besselK (d - 1) x + (v + d) / x * besselK d x < besselK m x := by
  rcases hd.eq_or_lt with hzero | hpos
  · rw [← hzero] at hm hdv ⊢
    have hz := besselK_zero_order_comparison hx hdv (by simpa using hm)
    have hk := besselK_neg 1 x
    norm_num only [zero_sub, add_zero, zero_pow, zero_add] at hk ⊢
    rw [hk]
    exact hz
  · have h := besselK_three_order hx hpos hdv hm
    have hr := eq_add_of_sub_eq (besselK_recurrence hx d)
    have heq : (v + d) * besselK (d + 1) x + (d - v) * besselK (d - 1) x =
        (2 * d) * (besselK (d - 1) x + (v + d) / x * besselK d x) := by
      rw [hr]
      ring
    rw [heq] at h
    exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 * d)).mp h

theorem weightedK_hasDerivAt {x : ℝ} (hx : 0 < x) (v d : ℝ) :
    HasDerivAt (weightedK v d)
      (-(weightedK v (d - 1) x + (v + d) * weightedK (v + 1) d x)) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x) (p := -v)
    (Or.inl (ne_of_gt hx))).mul (besselK_hasDerivAt_lower hx d)
  convert! h using 1
  simp only [weightedK]
  have heq : x ^ (-(v + 1)) = x ^ (-v) / x := by
    rw [show -(v + 1) = -v - 1 by ring, Real.rpow_sub hx]
    simp only [Real.rpow_one]
  have heq' : x ^ (-v - 1) = x ^ (-v) / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [heq, heq']
  ring

theorem weightedK_derivative_integrableOn {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) (d : ℝ) :
    IntegrableOn (fun x => -(weightedK v (d - 1) x + (v + d) * weightedK (v + 1) d x))
      (Ioi a) := by
  exact ((weightedK_integrableOn hv ha (d - 1)).add
    ((weightedK_integrableOn (by linarith : 0 ≤ v + 1) ha d).const_mul (v + d))).neg

theorem weightedK_derivative_integral {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) (d : ℝ) :
    (∫ x in Ioi a, -(weightedK v (d - 1) x + (v + d) * weightedK (v + 1) d x)) =
      -weightedK v d a := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => weightedK_hasDerivAt (ha.trans_le hx) v d)
    (weightedK_derivative_integrableOn hv ha d) (weightedK_tendsto_zero hv d)
  simpa only [zero_sub] using hi

theorem tail_strict_lower_bound {x d v m : ℝ} (hx : 0 < x)
    (hd : 0 ≤ d) (hdv : d < v) (hm : m ^ 2 = d ^ 2 + 2 * v + 1) :
    weightedK v d x < ∫ t in Ioi x, weightedK v m t := by
  have hv : 0 ≤ v := hd.trans hdv.le
  let f : ℝ → ℝ := fun t => weightedK v (d - 1) t + (v + d) * weightedK (v + 1) d t
  have hf : IntegrableOn f (Ioi x) := (weightedK_integrableOn hv hx (d - 1)).add
    ((weightedK_integrableOn (by linarith : 0 ≤ v + 1) hx d).const_mul (v + d))
  have hg := weightedK_integrableOn hv hx m
  have hfg : ∀ t ∈ Ioi x, f t < weightedK v m t := by
    intro t ht
    have ht0 := hx.trans ht
    have h := mul_lt_mul_of_pos_left (besselK_differential_comparison ht0 hd hdv hm)
      (Real.rpow_pos_of_pos ht0 (-v))
    dsimp [f, weightedK]
    have heq : t ^ (-(v + 1)) = t ^ (-v) / t := by
      rw [show -(v + 1) = -v - 1 by ring, Real.rpow_sub ht0, Real.rpow_one]
    rw [heq]
    convert h using 1
    ring
  have hn : 0 ≤ᵐ[volume.restrict (Ioi x)] (fun t => weightedK v m t - f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (sub_pos.mpr (hfg t ht)).le
  have hsub : Ioo (x + 1) (x + 2) ⊆
      Function.support (fun t => weightedK v m t - f t) ∩ Ioi x := by
    intro t ht
    have htx : x < t := by linarith [ht.1]
    exact ⟨ne_of_gt (sub_pos.mpr (hfg t htx)), htx⟩
  have hp := (setIntegral_pos_iff_support_of_nonneg_ae hn (hg.sub hf)).2
    (lt_of_lt_of_le (by simp only [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith))
      (measure_mono hsub))
  rw [integral_sub hg hf] at hp
  have hi := weightedK_derivative_integral hv hx d
  change (∫ t in Ioi x, -f t) = -weightedK v d x at hi
  rw [integral_neg] at hi
  have heq : ∫ t in Ioi x, f t = weightedK v d x := neg_injective hi
  rw [heq] at hp
  exact sub_pos.mp hp

end GauntIntegral
