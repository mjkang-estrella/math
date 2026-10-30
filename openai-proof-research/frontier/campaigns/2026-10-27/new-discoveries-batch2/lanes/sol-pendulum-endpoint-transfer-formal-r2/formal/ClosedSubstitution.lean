module
public import Substitution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public section
noncomputable section
open Real MeasureTheory Set
namespace PendulumTimeMap
theorem closed_change_range {c q x : ℝ} (hc : 0<c) (hq : q≤Real.pi/2)
 (hx : x∈Icc 0 q) : change c x ∈ Icc 0 (change c q) := by
 have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2*x) (y := 2*q) (by linarith [hx.1]) (by linarith) (by linarith [hx.2])
 have h := Real.cos_le_one (2*x)
 constructor <;> unfold change <;> nlinarith
theorem closed_change_sqrt {c q x : ℝ} (hc : 0<c) (hq : q≤Real.pi/2)
 (hx : x∈Ioo 0 q) : Real.sqrt (change c x*(c-change c x)) = c/2*Real.sin (2*x) := by
 have hs : 0<Real.sin (2*x) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
 have he : change c x*(c-change c x)=(c/2*Real.sin (2*x))^2 := by
   unfold change
   have ht := Real.sin_sq_add_cos_sq (2*x)
   linear_combination -(c^2/4)*ht
 rw [he, Real.sqrt_sq (by positivity)]
theorem closed_weighted_substitution {c q : ℝ} (hc : 0<c) (hq0 : 0<q) (hq : q≤Real.pi/2)
 (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 (change c q))) :
 IntervalIntegrable (fun t => w t / Real.sqrt (t*(c-t))) volume 0 (change c q) ∧
 (∫ t in 0..change c q, w t / Real.sqrt (t*(c-t))) =
 2*(∫ x in 0..q, w (change c x)) := by
 have hr : ∀ x∈Icc 0 q, change c x∈Icc 0 (change c q) := fun x hx => closed_change_range hc hq hx
 have hwc : ContinuousOn (fun x => w (change c x)) (Icc 0 q) := hw.comp (change_cont c).continuousOn hr
 have hint : IntervalIntegrable (fun x => 2*w (change c x)) volume 0 q :=
   (continuousOn_const.mul hwc).intervalIntegrable_of_Icc hq0.le
 have heq : EqOn (fun x => (w (change c x) / Real.sqrt (change c x*(c-change c x)))*changeDeriv c x)
   (fun x => 2*w (change c x)) (uIoo 0 q) := by
   rw [uIoo_of_lt hq0]
   intro x hx
   dsimp only
   rw [closed_change_sqrt hc hq hx]
   have hs : Real.sin (2*x) ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))
   unfold changeDeriv
   field_simp
 have hd : ∀ x∈Ioo (min 0 q) (max 0 q), HasDerivAt (change c) (changeDeriv c x) x := fun x _ => change_deriv c x
 have hn : ∀ x∈Ioo (min 0 q) (max 0 q), 0≤changeDeriv c x := by
   simp only [min_eq_left hq0.le, max_eq_right hq0.le]
   intro x hx
   exact le_of_lt (mul_pos hc (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])))
 have hz : change c 0=0 := by simp [change]
 have hi := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
   (g := fun t => w t / Real.sqrt (t*(c-t)))
   (change_cont c).continuousOn hd hn).mp (hint.congr_uIoo heq.symm)
 rw [hz] at hi
 refine ⟨hi, ?_⟩
 have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
   (g := fun t => w t / Real.sqrt (t*(c-t))) (change_cont c).continuousOn hd hn
 simp only [Function.comp_apply] at h
 rw [hz, intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_const_mul] at h
 exact h.symm
end PendulumTimeMap
