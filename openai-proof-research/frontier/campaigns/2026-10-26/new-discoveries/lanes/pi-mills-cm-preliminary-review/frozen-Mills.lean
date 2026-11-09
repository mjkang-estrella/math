import Mathlib

open MeasureTheory Set
open scoped Interval

namespace MillsCounterexample

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-(1 / 2 : ℝ) * x ^ 2)

noncomputable def mills (x : ℝ) : ℝ :=
  Real.exp (x ^ 2 / 2) * ∫ t in Ioi x, gaussian t

theorem gaussian_integrable : Integrable gaussian :=
  integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)

theorem gaussian_continuous : Continuous gaussian := by
  unfold gaussian
  fun_prop

theorem gaussian_half_integral :
    (∫ t in Ioi (0 : ℝ), gaussian t) = Real.sqrt (2 * Real.pi) / 2 := by
  simpa [gaussian, div_eq_mul_inv, mul_comm] using integral_gaussian_Ioi (1 / 2 : ℝ)

theorem mills_eq_finite_integral (x : ℝ) :
    mills x = Real.exp (x ^ 2 / 2) *
      (Real.sqrt (2 * Real.pi) / 2 - ∫ t in (0 : ℝ)..x, gaussian t) := by
  have hh := intervalIntegral.integral_Ioi_sub_Ioi'
    (gaussian_integrable.integrableOn (s := Ioi (0 : ℝ)))
    (gaussian_integrable.integrableOn (s := Ioi x))
  rw [gaussian_half_integral] at hh
  unfold mills
  congr 1
  linarith

theorem mills_zero : mills 0 = Real.sqrt (2 * Real.pi) / 2 := by
  simp [mills_eq_finite_integral]

theorem mills_zero_sq : mills 0 ^ 2 = Real.pi / 2 := by
  rw [mills_zero]
  have h := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

theorem mills_hasDerivAt (x : ℝ) : HasDerivAt mills (x * mills x - 1) x := by
  have hg := intervalIntegral.integral_hasDerivAt_right
    (gaussian_continuous.intervalIntegrable (0 : ℝ) x)
    (gaussian_continuous.stronglyMeasurableAtFilter volume (nhds x))
    gaussian_continuous.continuousAt
  have he : HasDerivAt (fun y : ℝ => Real.exp (y ^ 2 / 2))
      (x * Real.exp (x ^ 2 / 2)) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).exp using 1 <;>
      simp [Pi.pow_apply, mul_comm]
  have hh := he.mul ((hasDerivAt_const x (Real.sqrt (2 * Real.pi) / 2)).sub hg)
  simp only [Pi.sub_apply] at hh
  have hprod : Real.exp (x ^ 2 / 2) * gaussian x = 1 := by
    rw [gaussian, ← Real.exp_add]
    rw [show x ^ 2 / 2 + -(1 / 2 : ℝ) * x ^ 2 = 0 by ring, Real.exp_zero]
  convert hh using 1
  · funext y
    exact mills_eq_finite_integral y
  · rw [mills_eq_finite_integral]
    nlinarith [hprod]

theorem mills_deriv : deriv mills = fun x => x * mills x - 1 := by
  funext x
  exact (mills_hasDerivAt x).deriv

theorem mills_contDiff_nat (n : ℕ) : ContDiff ℝ n mills := by
  induction n with
  | zero =>
      exact contDiff_zero.mpr
        (continuous_iff_continuousAt.mpr (fun x => (mills_hasDerivAt x).continuousAt))
  | succ n hn =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (mills_hasDerivAt x).differentiableAt, ?_, ?_⟩
      · intro h
        simp at h
      · rw [mills_deriv]
        exact (contDiff_id.mul hn).sub contDiff_const

noncomputable def quotient (x : ℝ) : ℝ := -(mills x) ^ 2 / deriv mills x

theorem quotient_eq (x : ℝ) : quotient x = mills x ^ 2 / (1 - x * mills x) := by
  simp only [quotient, mills_deriv]
  rw [show 1 - x * mills x = -(x * mills x - 1) by ring, div_neg]
  ring

end MillsCounterexample
