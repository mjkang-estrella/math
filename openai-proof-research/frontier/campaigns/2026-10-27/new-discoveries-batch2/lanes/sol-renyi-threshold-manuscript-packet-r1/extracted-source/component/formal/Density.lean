module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Tactic.FieldSimp
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
@[expose] noncomputable def normalizer (a : ℝ) : ℝ := (1-exp (-a))⁻¹
@[expose] noncomputable def density (a x : ℝ) : ℝ :=
  (Icc 0 a).indicator (fun x => normalizer a * exp (-x)) x
@[expose] noncomputable def exponential (x : ℝ) : ℝ :=
  (Ici 0).indicator (fun x => exp (-x)) x
@[expose] noncomputable def convolution (f g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t : ℝ, f t * g (s-t)
@[expose] noncomputable def moment (p : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, (f x)^p
@[expose] noncomputable def entropy (p : ℝ) (f : ℝ → ℝ) : ℝ := log (moment p f)/(1-p)

theorem normalizer_pos {a : ℝ} (ha : 0 < a) : 0 < normalizer a := by
  unfold normalizer
  apply inv_pos.mpr
  have H : exp (-a) < 1 := by simpa using exp_lt_exp.mpr (neg_neg_of_pos ha)
  exact sub_pos.mpr H

theorem density_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ density a x := by
  exact indicator_nonneg (fun _ _ => mul_nonneg (normalizer_pos ha).le (exp_pos _).le) x

theorem density_integrable (a : ℝ) : Integrable (density a) := by
  unfold density
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact Continuous.integrableOn_Icc (by fun_prop)

theorem exp_interval (q a : ℝ) (hq : q ≠ 0) :
    (∫ x in (0:ℝ)..a, exp (-q*x)) = (1-exp (-q*a))/q := by
  rw [show (fun x : ℝ => exp (-q*x)) = (fun x => exp ((-q)*x)) by rfl,
    intervalIntegral.integral_comp_mul_left exp (neg_ne_zero.mpr hq), integral_exp]
  simp only [mul_zero, exp_zero, smul_eq_mul]
  field_simp
  ring

theorem density_integral {a : ℝ} (ha : 0 < a) : ∫ x : ℝ, density a x = 1 := by
  unfold density
  rw [integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
  have he := exp_interval 1 a one_ne_zero
  simp only [neg_mul, one_mul, div_one] at he
  rw [he]
  exact inv_mul_cancel₀ (ne_of_gt (inv_pos.mp (normalizer_pos ha)))
theorem convolution_integrand (a s t : ℝ) :
    density a t * density a (s-t) =
    (Icc (max 0 (s-a)) (min a s)).indicator
      (fun _ => normalizer a ^ 2 * exp (-s)) t := by
  have he : t ∈ Icc (max 0 (s-a)) (min a s) ↔
      t ∈ Icc 0 a ∧ s-t ∈ Icc 0 a := by
    simp only [mem_Icc, max_le_iff, le_min_iff]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  by_cases h1 : t ∈ Icc 0 a
  · by_cases h2 : s-t ∈ Icc 0 a
    · simp only [density, indicator_of_mem h1, indicator_of_mem h2,
        indicator_of_mem (he.mpr ⟨h1,h2⟩)]
      rw [show -s = -t + -(s-t) by ring, exp_add]
      ring
    · simp [density, h1, h2, show t ∉ Icc (max 0 (s-a)) (min a s) from
        fun h => h2 (he.mp h).2]
  · simp [density, h1, show t ∉ Icc (max 0 (s-a)) (min a s) from
      fun h => h1 (he.mp h).1]

theorem convolution_integrable (a s : ℝ) :
    Integrable (fun t => density a t*density a (s-t)) := by
  simp_rw [convolution_integrand]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)

theorem convolution_formula (a s : ℝ) :
    convolution (density a) (density a) s =
      (volume (Icc (max 0 (s-a)) (min a s))).toReal *
        (normalizer a ^ 2 * exp (-s)) := by
  unfold convolution
  simp_rw [convolution_integrand]
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul]
  rfl
end Renyi
