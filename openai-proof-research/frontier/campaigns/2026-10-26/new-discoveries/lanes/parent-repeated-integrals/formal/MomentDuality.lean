import MeasureMoments

open MeasureTheory Set Filter
open scoped BigOperators

namespace RepeatedIntegrals

noncomputable section

def momentPairing {n : ℕ} (a y : MomentSpace n) : ℝ := ∑ i, a i * y i

def momentPolynomial {n : ℕ} (a : MomentSpace n) : Polynomial ℝ :=
  Polynomial.ofFn (n + 1) a

theorem momentPolynomial_eval {n : ℕ} (a : MomentSpace n) (t : ℝ) :
    (momentPolynomial a).eval t = momentPairing a (momentCurve n t) := by
  classical
  simp [momentPolynomial, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    momentPairing, momentCurve]

theorem momentPolynomial_ne_zero {n : ℕ} {a : MomentSpace n} (ha : a ≠ 0) :
    momentPolynomial a ≠ 0 := by
  intro h
  apply ha
  exact (Polynomial.injective_ofFn (n + 1)) (h.trans (Polynomial.ofFn_zero _).symm)

theorem momentPairing_integral {n : ℕ} (a : MomentSpace n) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) :
    momentPairing a (measureMoments n μ) = ∫ t, (momentPolynomial a).eval t ∂μ := by
  simp only [momentPairing, measureMoments]
  simp_rw [momentPolynomial_eval, momentPairing, momentCurve]
  rw [integral_finsetSum _ (fun i _ => (supported_power_integrable hs i.val).const_mul (a i))]
  simp only [integral_const_mul]

theorem momentPairing_density {n : ℕ} (a : MomentSpace n) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    momentPairing a (densityMoments n ρ) =
      ∫ t in (0 : ℝ)..1, (momentPolynomial a).eval t * ρ t := by
  simp only [momentPolynomial_eval, momentPairing, momentCurve, densityMoments]
  simp_rw [Finset.sum_mul]
  have hi (i : Fin (n + 1)) : Continuous (fun t : ℝ => a i * t ^ i.val * ρ t) := by
    fun_prop
  rw [intervalIntegral.integral_finsetSum (f := fun (i : Fin (n + 1)) (t : ℝ) =>
    a i * t ^ i.val * ρ t) (fun i _ => (hi i).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change a i * (t ^ i.val * ρ t) = _
  ring

def dualCoefficients {n : ℕ} (L : MomentSpace n →L[ℝ] ℝ) : MomentSpace n :=
  fun i => L (Pi.single i 1)

theorem dualCoefficients_pairing {n : ℕ} (L : MomentSpace n →L[ℝ] ℝ) (y : MomentSpace n) :
    L y = momentPairing (dualCoefficients L) y := by
  classical
  have hy : y = ∑ i : Fin (n + 1), y i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← hy]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem momentPolynomial_integrable {n : ℕ} (a : MomentSpace n) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) :
    Integrable (fun t => (momentPolynomial a).eval t) μ := by
  simp only [momentPolynomial_eval, momentPairing, momentCurve]
  exact integrable_finsetSum _ (fun i _ => (supported_power_integrable hs i.val).const_mul (a i))

theorem atomless_moment_strict_positive {n : ℕ} (a : MomentSpace n) (ha : a ≠ 0)
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) (hm : 0 < μ.real univ)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ momentPairing a (momentCurve n t)) :
    0 < momentPairing a (measureMoments n μ) := by
  rw [momentPairing_integral a hs]
  have hz := (Polynomial.finite_setOfPred_isRoot (momentPolynomial_ne_zero ha)).countable.ae_notMem μ
  have hp : ∀ᵐ t ∂μ, 0 < (momentPolynomial a).eval t := by
    filter_upwards [ae_mem_unit_interval hs, hz] with t ht hzt
    exact lt_of_le_of_ne (by rw [momentPolynomial_eval]; exact hn t ht)
      (Ne.symm hzt)
  have hi := momentPolynomial_integrable a hs
  have hn' : 0 ≤ᵐ[μ] fun t => (momentPolynomial a).eval t := hp.mono (fun _ h => h.le)
  have hnonzero : ¬ (fun t => (momentPolynomial a).eval t) =ᵐ[μ] 0 := by
    intro he
    have hf : ∀ᵐ _t : ℝ ∂μ, False := by
      filter_upwards [hp, he] with t ht heq
      simp only [Pi.zero_apply] at heq
      rw [heq] at ht
      exact (lt_irrefl 0 ht)
    have hμ : μ univ = 0 := by simpa only [ae_iff, not_false_eq_true, ofPred_true] using hf
    have : μ.real univ = 0 := by simp [Measure.real, hμ]
    linarith
  have hne : (∫ t, (momentPolynomial a).eval t ∂μ) ≠ 0 :=
    mt (integral_eq_zero_iff_of_nonneg_ae hn' hi).mp hnonzero
  exact lt_of_le_of_ne (integral_nonneg_of_ae hn') (Ne.symm hne)

end

end RepeatedIntegrals
