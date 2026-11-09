import PolynomialConvexity.Model

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Finset Set Filter

instance expOne_probability : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure zero_lt_one

instance expOne_noAtoms : NullSingletonClass (expMeasure (1 : ℝ)) := by
  unfold expMeasure gammaMeasure
  infer_instance

theorem expOne_tail (t : ℝ) (ht : 0 ≤ t) :
    expMeasure 1 (Ici t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [← measure_congr (Ioi_ae_eq_Ici (μ := expMeasure 1)), ← compl_Iic,
    measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf, cdf_expMeasure_eq zero_lt_one, ite_eq_left ht, one_mul]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · congr 1
    ring
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

theorem expOne_nonneg : ∀ᵐ t : ℝ ∂expMeasure 1, 0 ≤ t := by
  have h : expMeasure 1 (Iio 0) = 0 := by
    rw [measure_congr (Iio_ae_eq_Iic (μ := expMeasure 1)), ← ofReal_cdf,
      cdf_expMeasure_eq zero_lt_one]
    simp
  apply ae_iff.mpr
  have hs : {a : ℝ | ¬0 ≤ a} = Set.Iio 0 := by
    ext a
    exact not_le
  rw [hs]
  exact h

theorem clocks_nonneg (n : ℕ) : ∀ᵐ ω ∂clockMeasure n, ∀ v, 0 ≤ ω v := by
  rw [ae_all_iff]
  intro v
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => expMeasure 1)).eventually expOne_nonneg

theorem vertexThreshold_nonneg {n L d : ℕ} (e : Fin d → Edge n L)
    (t : Fin d → ℝ) (v : Fin n) : 0 ≤ vertexThreshold e t v := by
  exact ((vertexThreshold_le e t v _).1 le_rfl).1

theorem joint_survival {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (t : Fin d → ℝ) :
    clockMeasure n {ω | ∀ i, t i ≤ lifetime hL (e i) ω} =
      ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v)) := by
  calc
    _ = clockMeasure n {ω | (∀ v, 0 ≤ ω v) ∧ ∀ i, t i ≤ lifetime hL (e i) ω} := by
      apply measure_congr
      filter_upwards [clocks_nonneg n] with ω hω
      exact propext ⟨fun h => ⟨hω, h⟩, fun h => h.2⟩
    _ = ∏ v, expMeasure 1 (Ici (vertexThreshold e t v)) := joint_event_probability hL e t
    _ = ∏ v, ENNReal.ofReal (Real.exp (-vertexThreshold e t v)) := by
      apply prod_congr rfl
      intro v _
      exact expOne_tail _ (vertexThreshold_nonneg e t v)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => (Real.exp_pos _).le),
        ← Real.exp_sum, sum_neg_distrib]

end
end PolynomialConvexity
