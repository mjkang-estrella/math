module
public import InputMoment
public import Mathlib.Tactic.Linarith
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
@[expose] noncomputable def tent (a s : ℝ) : ℝ := max (min a s - max 0 (s-a)) 0

theorem convolution_tent (a s : ℝ) : convolution (density a) (density a) s =
    tent a s * (normalizer a ^ 2 * exp (-s)) := by
  rw [convolution_formula, Real.volume_Icc]
  unfold tent
  by_cases h : 0 ≤ min a s - max 0 (s-a)
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h), ENNReal.toReal_zero,
      max_eq_right (le_of_not_ge h)]

theorem tent_zero_off {a s : ℝ} (_ha : 0 < a) (hs : s ∉ Icc 0 (2*a)) : tent a s = 0 := by
  unfold tent
  apply max_eq_right
  by_cases h : s < 0
  · have h1 : min a s ≤ s := min_le_right _ _
    have h2 : 0 ≤ max 0 (s-a) := le_max_left _ _
    linarith
  · have h' : 2*a < s := by simp only [mem_Icc, not_and_or, not_le] at hs; rcases hs with hs|hs; contradiction; exact hs
    have h1 : min a s ≤ a := min_le_left _ _
    have h2 : s-a ≤ max 0 (s-a) := le_max_right _ _
    linarith

theorem tent_first {a s : ℝ} (hs : s ∈ Icc 0 a) : tent a s = s := by
  rw [tent, min_eq_right hs.2, max_eq_left (show s-a ≤ 0 by linarith [hs.2]),
    sub_zero, max_eq_left hs.1]

theorem tent_second {a s : ℝ} (hs : s ∈ Icc a (2*a)) : tent a s = 2*a-s := by
  rw [tent, min_eq_left hs.1, max_eq_right (show 0 ≤ s-a by linarith [hs.1])]
  rw [max_eq_left (show 0 ≤ a-(s-a) by linarith [hs.2])]
  ring

theorem convolution_power_integrable {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    Integrable (fun s => (convolution (density a) (density a) s)^p) := by
  have he : (fun s => (convolution (density a) (density a) s)^p) =
      (Icc 0 (2*a)).indicator (fun s => (tent a s*(normalizer a^2*exp (-s)))^p) := by
    funext s
    by_cases hs : s ∈ Icc 0 (2*a)
    · simp only [indicator_of_mem hs, convolution_tent]
    · simp [indicator_of_notMem hs, convolution_tent, tent_zero_off ha hs,
        zero_rpow hp.ne']
  rw [he]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Continuous.integrableOn_Icc
  have hp0 : 0 ≤ p := hp.le
  unfold tent
  fun_prop
theorem convolution_nonneg (a s : ℝ) : 0 ≤ convolution (density a) (density a) s := by
  rw [convolution_tent]
  exact mul_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) (exp_pos _).le)

theorem convolution_moment_pos {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    0 < moment p (convolution (density a) (density a)) := by
  apply (integral_pos_iff_support_of_nonneg
    (fun s => rpow_nonneg (convolution_nonneg a s) p)
    (convolution_power_integrable ha hp)).mpr
  have hs : Ioo 0 a ⊆ Function.support
      (fun s => (convolution (density a) (density a) s)^p) := by
    intro s hs
    apply (rpow_pos_of_pos _ p).ne'
    rw [convolution_tent, tent_first ⟨hs.1.le,hs.2.le⟩]
    exact mul_pos hs.1 (mul_pos (sq_pos_of_pos (normalizer_pos ha)) (exp_pos _))
  have H := measure_mono (μ := volume) hs
  have H0 : 0 < volume (Ioo 0 a) := by simpa using ha
  exact H0.trans_le H
end Renyi
