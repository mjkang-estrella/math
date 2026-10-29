module
public import Deficit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
theorem exponential_nonneg (x : ℝ) : 0 ≤ exponential x :=
  indicator_nonneg (fun _ _ => (exp_pos _).le) x

theorem exponential_integrable : Integrable exponential := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_neg_Ioi 0)

theorem exponential_integral : (∫ x : ℝ, exponential x) = 1 := by
  unfold exponential
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_neg_Ioi_zero]

theorem exponential_logConcave : LogConcaveDensity exponential := by
  refine ⟨exponential_nonneg, ?_⟩
  intro x y t ht ht1
  have ht' : 0 < 1-t := sub_pos.mpr ht1
  by_cases hx : x ∈ Ici (0:ℝ)
  · by_cases hy : y ∈ Ici (0:ℝ)
    · have hz : t*x+(1-t)*y ∈ Ici (0:ℝ) :=
        add_nonneg (mul_nonneg ht.le hx) (mul_nonneg ht'.le hy)
      simp only [exponential, indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz]
      rw [← exp_mul, ← exp_mul, ← exp_add, show -x*t + -y*(1-t) = -(t*x+(1-t)*y) by ring_nf]
    · rw [show exponential y=0 by simp [exponential,hy], zero_rpow ht'.ne', mul_zero]
      exact exponential_nonneg _
  · rw [show exponential x=0 by simp [exponential,hx], zero_rpow ht.ne', zero_mul]
    exact exponential_nonneg _

theorem exponential_power {p : ℝ} (hp : 0 < p) (x : ℝ) :
    (exponential x)^p = (Ici 0).indicator (fun x => exp (-p*x)) x := by
  by_cases hx : x ∈ Ici (0:ℝ)
  · simp only [exponential, indicator_of_mem hx]
    rw [← exp_mul, show -x*p = -p*x by ring_nf]
  · simp [exponential,hx,zero_rpow hp.ne']

theorem exponential_power_integrable {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => (exponential x)^p) := by
  simp_rw [exponential_power hp]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) 0)

theorem exponential_moment {p : ℝ} (hp : 0 < p) : moment p exponential = 1/p := by
  unfold moment
  simp_rw [exponential_power hp]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos hp) 0]
  simp

theorem exponential_convolution_integrand (s t : ℝ) :
    exponential t * exponential (s-t) = (Icc 0 s).indicator (fun _ => exp (-s)) t := by
  have he : t ∈ Icc 0 s ↔ t ∈ Ici (0:ℝ) ∧ s-t ∈ Ici (0:ℝ) := by
    simp only [mem_Icc, mem_Ici]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  by_cases hx : t ∈ Ici (0:ℝ)
  · by_cases hy : s-t ∈ Ici (0:ℝ)
    · simp only [exponential, indicator_of_mem hx, indicator_of_mem hy,
        indicator_of_mem (he.mpr ⟨hx,hy⟩)]
      rw [← exp_add, show -t + -(s-t) = -s by ring_nf]
    · simp [exponential,hx,hy,show t ∉ Icc 0 s from fun h => hy (he.mp h).2]
  · simp [exponential,hx,show t ∉ Icc 0 s from fun h => hx (he.mp h).1]

theorem exponential_convolution_integrable (s : ℝ) :
    Integrable (fun t => exponential t * exponential (s-t)) := by
  simp_rw [exponential_convolution_integrand]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)

theorem exponential_convolution (s : ℝ) :
    convolution exponential exponential s = (Ici 0).indicator (fun s => exp (-s)*s) s := by
  unfold convolution
  simp_rw [exponential_convolution_integrand]
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc]
  by_cases hs : s ∈ Ici (0:ℝ)
  · rw [indicator_of_mem hs, sub_zero, ENNReal.toReal_ofReal hs, mul_comm]
  · rw [indicator_of_notMem hs, ENNReal.ofReal_eq_zero.mpr (by simp at hs; linarith),
      ENNReal.toReal_zero, zero_mul]

theorem exponential_convolution_nonneg (s : ℝ) :
    0 ≤ convolution exponential exponential s := by
  rw [exponential_convolution]
  exact indicator_nonneg (fun s hs => mul_nonneg (exp_pos _).le hs) s

theorem exponential_convolution_power {p : ℝ} (hp : 0 < p) (s : ℝ) :
    (convolution exponential exponential s)^p =
      (Ioi 0).indicator (fun s => exp (-p*s)*s^p) s := by
  rw [exponential_convolution]
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ici (0:ℝ) from hs.le), indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs),
      mul_rpow (exp_pos _).le hs.le, ← exp_mul, show -s*p = -p*s by ring_nf]
  · by_cases hz : s = 0
    · subst s; simp [zero_rpow hp.ne']
    · rw [indicator_of_notMem (show s ∉ Ici (0:ℝ) by simp only [mem_Ici]; exact lt_of_le_of_ne (le_of_not_gt hs) hz |> fun h => not_le.mpr h),
        indicator_of_notMem (show s ∉ Ioi (0:ℝ) from hs), zero_rpow hp.ne']

theorem exponential_convolution_power_integrable {p : ℝ} (hp : 0 < p) :
    Integrable (fun s => (convolution exponential exponential s)^p) := by
  simp_rw [exponential_convolution_power hp]
  exact (moment_integrable hp).integrable_indicator measurableSet_Ioi

theorem exponential_convolution_moment {p : ℝ} (hp : 0 < p) :
    moment p (convolution exponential exponential) = J p := by
  unfold moment
  simp_rw [exponential_convolution_power hp]
  exact integral_indicator measurableSet_Ioi

theorem exponential_ratio {p : ℝ} (hp : 0 < p) :
    moment p (convolution exponential exponential) / moment p exponential = p*J p := by
  rw [exponential_convolution_moment hp, exponential_moment hp]
  field_simp
end Renyi
