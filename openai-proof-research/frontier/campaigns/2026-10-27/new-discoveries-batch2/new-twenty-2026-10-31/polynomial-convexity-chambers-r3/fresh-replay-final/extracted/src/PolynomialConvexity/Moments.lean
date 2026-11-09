import PolynomialConvexity.Tails
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

theorem gamma_nat_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ k) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h

theorem gamma_nat_integral (k : ℕ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ k) = (Nat.factorial k : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h.symm

theorem expOne_density (t : ℝ) :
    (gammaPDF 1 1 t).toReal = (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) t := by
  change (exponentialPDF 1 t).toReal = _
  rw [exponentialPDF_eq]
  by_cases ht : 0 ≤ t
  · simp [ht, ENNReal.toReal_ofReal, (Real.exp_pos (-t)).le]
  · simp [ht]

theorem expOne_power_integrable (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  rw [integrable_withDensity_iff (show Measurable (gammaPDF 1 1) from (measurable_gammaPDFReal 1 1).ennreal_ofReal)
    (Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  have h : (fun t : ℝ => t ^ k * (gammaPDF 1 1 t).toReal) =
      (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t) * t ^ k) := by
    funext t
    rw [expOne_density]
    by_cases ht : 0 ≤ t <;> simp [ht, mul_comm]
  rw [h, integrable_indicator_iff measurableSet_Ici]
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (gamma_nat_integrable k)

theorem expOne_power_integral (k : ℕ) :
    (∫ t : ℝ, t ^ k ∂expMeasure 1) = (Nat.factorial k : ℝ) := by
  unfold expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (gammaPDF 1 1) from (measurable_gammaPDFReal 1 1).ennreal_ofReal)
    (Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, expOne_density]
  have h : (fun t : ℝ => (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t)) t * t ^ k) =
      (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t) * t ^ k) := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [h, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact gamma_nat_integral k

end
end PolynomialConvexity
