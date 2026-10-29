module
public import Density
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
theorem density_power {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (x : ℝ) :
    (density a x)^p = (Icc 0 a).indicator
      (fun x => (normalizer a)^p * exp (-p*x)) x := by
  by_cases hx : x ∈ Icc 0 a
  · simp only [density, indicator_of_mem hx]
    rw [mul_rpow (normalizer_pos ha).le (exp_pos _).le, ← exp_mul]
    congr 2
    ring
  · simp [density, hx, zero_rpow hp.ne']

theorem density_power_integrable {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    Integrable (fun x => (density a x)^p) := by
  simp_rw [density_power ha hp]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact Continuous.integrableOn_Icc (by fun_prop)

theorem density_moment {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    moment p (density a) = (normalizer a)^p * ((1-exp (-p*a))/p) := by
  unfold moment
  simp_rw [density_power ha hp]
  rw [integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le,
    exp_interval p a hp.ne']

theorem density_moment_pos {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    0 < moment p (density a) := by
  rw [density_moment ha hp]
  apply mul_pos (rpow_pos_of_pos (normalizer_pos ha) p)
  apply div_pos _ hp
  apply sub_pos.mpr
  have H : -p*a < 0 := by simpa only [neg_mul] using neg_neg_of_pos (mul_pos hp ha)
  simpa using exp_lt_exp.mpr H
end Renyi
