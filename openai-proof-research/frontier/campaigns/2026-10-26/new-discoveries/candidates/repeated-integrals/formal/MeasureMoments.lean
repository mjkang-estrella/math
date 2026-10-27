import MomentTransform
import SourceMeasure

open MeasureTheory Set Filter
open scoped BigOperators

namespace RepeatedIntegrals

noncomputable section

def measureMoments (n : ℕ) (μ : Measure ℝ) : MomentSpace n := fun i => ∫ t, t ^ i.val ∂μ

theorem ae_mem_unit_interval {μ : Measure ℝ} (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) :
    ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := by
  exact ae_iff.mpr hs

theorem supported_power_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) (k : ℕ) : Integrable (fun t : ℝ => t ^ k) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_id.pow k).aestronglyMeasurable
  filter_upwards [ae_mem_unit_interval hs] with t ht
  change ‖t ^ k‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 _)]
  exact pow_le_one₀ ht.1 ht.2

theorem endpointMomentTransform_measure (n : ℕ) {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) (j : Fin (n + 1)) :
    endpointMomentTransform n (measureMoments n μ) j =
      (∫ t, (1 - t) ^ (n - j.val) ∂μ) / ((n - j.val).factorial : ℝ) := by
  rw [endpointMomentTransform_apply]
  simp only [measureMoments]
  have hi (i : Fin (n + 1)) : Integrable (fun t : ℝ =>
      (((n - j.val).choose i.val : ℝ) * (-1) ^ i.val /
        ((n - j.val).factorial : ℝ)) * t ^ i.val) μ :=
    (supported_power_integrable hs i.val).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_div]
  congr 1
  funext t
  rw [← finite_binomial_kernel n (n - j.val) (Nat.sub_le _ _) t, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceMeasure_transform {n : ℕ} {b : MomentSpace n} (d : SourceMeasure n b) :
    endpointMomentTransform n (measureMoments n d.measure) = b := by
  have := d.finite
  funext j
  rw [endpointMomentTransform_measure n d.supported j]
  exact (d.jets j).symm

theorem measureMoments_integral {n : ℕ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) :
    measureMoments n μ = ∫ t, momentCurve n t ∂μ := by
  funext i
  exact (ContinuousLinearMap.proj i : MomentSpace n →L[ℝ] ℝ).integral_comp_comm
    (integrable_pi_iff.mpr (fun i => supported_power_integrable hs i.val))

end

end RepeatedIntegrals
