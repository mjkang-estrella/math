import PolynomialConvexity.Integrability
import Mathlib.MeasureTheory.Measure.Prod

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

theorem mixed_layercake {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    ENNReal.ofReal (∫ ω, ∏ i, lifetime hL (e i) ω ∂clockMeasure n) =
      ∫⁻ t : Fin d → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
        ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v)) := by
  let S : Set ((Fin n → ℝ) × (Fin d → ℝ)) :=
    {p | ∀ i, 0 < p.2 i ∧ p.2 i ≤ lifetime hL (e i) p.1}
  have hS : MeasurableSet S := by
    have heq : S = ⋂ i, {p : (Fin n → ℝ) × (Fin d → ℝ) | 0 < p.2 i ∧ p.2 i ≤ lifetime hL (e i) p.1} := by
      ext p
      simp only [S, mem_ofPred_eq, mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_snd)).inter
      (measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
        ((lifetime_measurable hL (e i)).comp measurable_fst))
  have hbox (ω : Fin n → ℝ) :
      Prod.mk ω ⁻¹' S = Set.pi Set.univ (fun i => Ioc (0 : ℝ) (lifetime hL (e i) ω)) := by
    ext t
    simp [S, Set.mem_pi]
  have hnonneg : ∀ᵐ ω ∂clockMeasure n, 0 ≤ ∏ i, lifetime hL (e i) ω :=
    (clocks_nonneg n).mono fun ω hω => Finset.prod_nonneg
      (fun i _ => lifetime_nonneg hL (e i) ω hω)
  rw [ofReal_integral_eq_lintegral_ofReal (mixed_integrable hL e) hnonneg]
  calc
    _ = ∫⁻ ω, volume (Prod.mk ω ⁻¹' S) ∂clockMeasure n := by
      apply lintegral_congr_ae
      filter_upwards [clocks_nonneg n] with ω hω
      rw [hbox, volume_pi_pi]
      simp only [Real.volume_Ioc, sub_zero]
      exact ENNReal.ofReal_prod_of_nonneg (fun i _ => lifetime_nonneg hL (e i) ω hω)
    _ = ((clockMeasure n).prod (volume : Measure (Fin d → ℝ))) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ t, clockMeasure n ((fun ω => (ω,t)) ⁻¹' S) := Measure.prod_apply_symm hS
    _ = ∫⁻ t, (Set.pi Set.univ (fun _ : Fin d => Ioi (0 : ℝ))).indicator
        (fun t => ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v))) t := by
      apply lintegral_congr
      intro t
      by_cases ht : ∀ i, 0 < t i
      · have hs : ((fun ω => (ω,t)) ⁻¹' S) = {ω | ∀ i, t i ≤ lifetime hL (e i) ω} := by
          ext ω
          simp [S, ht]
        rw [hs, joint_survival hL e]
        simp [Set.mem_pi, ht]
      · have hs : ((fun ω => (ω,t)) ⁻¹' S) = ∅ := by
          ext ω
          simp only [mem_preimage, mem_ofPred_eq, S, mem_empty_iff_false, iff_false]
          intro h
          exact ht (fun i => (h i).1)
        rw [hs, measure_empty]
        simp [Set.mem_pi, ht]
    _ = _ := lintegral_indicator (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)) _

end
end PolynomialConvexity
