module
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section
set_option autoImplicit false
set_option warningAsError true
open Real Filter Set
open scoped Topology
namespace Renyi

@[expose] noncomputable def bracket (p a u : ℝ) : ℝ :=
  (a + u) ^ p - (max (a - u) 0) ^ p

theorem bracket_bounds {p a u : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 ≤ a) (hu : 0 ≤ u) :
    0 ≤ bracket p a u ∧ bracket p a u ≤ (2*u)^p := by
  have hm : max (a-u) 0 ≤ a+u := max_le (by linarith) (by linarith)
  constructor
  · exact sub_nonneg.mpr (rpow_le_rpow (le_max_right _ _) hm hp.le)
  · by_cases h : u ≤ a
    · rw [bracket, max_eq_left (by linarith)]
      have H := Real.rpow_add_le_add_rpow (show 0 ≤ a-u by linarith)
        (show 0 ≤ 2*u by positivity) hp.le hp1.le
      rw [show a-u+2*u=a+u by ring] at H
      linarith
    · rw [bracket, max_eq_right (by linarith), zero_rpow hp.ne', sub_zero]
      exact rpow_le_rpow (by positivity) (by linarith) hp.le

theorem power_increment_le {p x y : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (hy : 0 ≤ y) :
    (x+y)^p-x^p ≤ p*y*x^(p-1) := by
  have H := rpow_one_add_le_one_add_mul_self
    (show -1 ≤ y/x by have := div_nonneg hy hx.le; linarith) hp.le hp1.le
  have H' := mul_le_mul_of_nonneg_left H (rpow_nonneg hx.le p)
  have hid : 1+y/x = (x+y)/x := by field_simp
  rw [hid, div_rpow (by positivity) hx.le] at H'
  rw [mul_div_cancel₀ _ (rpow_pos_of_pos hx p).ne'] at H'
  rw [rpow_sub hx, rpow_one]
  have he : x ^ p * (1 + p * (y / x)) = x^p + p*y*(x^p/x) := by ring
  rw [he] at H'
  linarith

theorem bracket_tendsto {p u : ℝ} (hp : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) :
    Tendsto (fun a : ℝ => bracket p a u) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => (a-u) ^ (p-1)) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < 1-p by linarith)).comp
      (show Tendsto (fun a : ℝ => a-u) atTop atTop from
        by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-u) tendsto_id)
    simpa [Function.comp_def] using H
  apply squeeze_zero' _ _ (by simpa using ht.const_mul (p*(2*u)))
  · filter_upwards [eventually_ge_atTop 0] with a ha
    exact (bracket_bounds hp hp1 ha hu).1
  · filter_upwards [eventually_gt_atTop u] with a ha
    rw [bracket, max_eq_left (by linarith)]
    have H := power_increment_le hp hp1 (show 0 < a-u by linarith)
      (show 0 ≤ 2*u by positivity)
    simpa [show a-u+2*u=a+u by ring, mul_assoc] using H

end Renyi
