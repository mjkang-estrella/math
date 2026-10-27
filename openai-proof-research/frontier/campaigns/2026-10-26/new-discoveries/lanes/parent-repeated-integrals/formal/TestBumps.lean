import EndpointBaseline

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace RepeatedIntegrals

noncomputable section

theorem exists_positive_test_bump {p : ℝ → ℝ} (hp : Continuous p) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hpt : 0 < p t) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (ψ =ᶠ[𝓝 (0 : ℝ)] fun _ => 0) ∧ (ψ =ᶠ[𝓝 (1 : ℝ)] fun _ => 0) ∧
      0 < ∫ x in (0 : ℝ)..1, p x * ψ x := by
  let U := Ioo (0 : ℝ) 1 ∩ {x | 0 < p x}
  have hU : IsOpen U := isOpen_Ioo.inter (isOpen_lt continuous_const hp)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU t ⟨ht, hpt⟩
  have hε0 : ε ≤ dist (0 : ℝ) t := by
    by_contra! h
    exact (hεU (mem_ball.mpr h)).1.1.false
  have hε1 : ε ≤ dist (1 : ℝ) t := by
    by_contra! h
    exact (lt_irrefl 1 (hεU (mem_ball.mpr h)).1.2)
  have hδ : 0 < ε / 2 := by positivity
  let ψ := endpointBump t (ε / 2) hδ
  have hs {x : ℝ} (hx : ψ x ≠ 0) : x ∈ U := by
    have hx' : x ∈ ball t (ε / 2) := by
      change x ∈ ball t ψ.rOut
      rw [← ψ.support_eq]
      exact hx
    exact hεU ((ball_subset_ball (by linarith : ε / 2 ≤ ε)) hx')
  have hn (x : ℝ) : 0 ≤ p x * ψ x := by
    by_cases hx : ψ x = 0
    · simp only [hx, mul_zero, le_refl]
    · exact mul_nonneg (hs hx).2.le (ψ.nonneg' x)
  have hc : HasCompactSupport (fun x => p x * ψ x) := ψ.hasCompactSupport.mul_left
  have hpos : 0 < ∫ x, p x * ψ x := by
    apply (hp.mul ψ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := t) hc hn
    have hc0 : ψ t = 1 := ψ.eventuallyEq_one.eq_of_nhds
    change p t * ψ t ≠ 0
    rw [hc0, mul_one]
    exact hpt.ne'
  refine ⟨ψ, ψ.contDiff, ψ.nonneg', ?_, ?_, ?_⟩
  · exact endpointBump_eventually_zero t (ε / 2) hδ 0 (by linarith)
  · exact endpointBump_eventually_zero t (ε / 2) hδ 1 (by linarith)
  · rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hpos
    · intro x hx
      have hz : ψ x = 0 := by
        by_contra h
        exact hx (Ioo_subset_Ioc_self (hs h).1)
      rw [hz, mul_zero]

theorem goodDensity_add_nonnegative_test {ρ ψ : ℝ → ℝ} (hρ : GoodDensity ρ)
    (hψ : ContDiff ℝ ∞ ψ) (hn : ∀ x, 0 ≤ ψ x)
    (h0 : ψ =ᶠ[𝓝 (0 : ℝ)] fun _ => 0) (h1 : ψ =ᶠ[𝓝 (1 : ℝ)] fun _ => 0)
    {a : ℝ} (ha : 0 ≤ a) : GoodDensity (fun x => ρ x + a * ψ x) := by
  refine ⟨hρ.1.add (contDiff_const.mul hψ), ?_, ?_, ?_⟩
  · intro t ht
    exact add_pos_of_pos_of_nonneg (hρ.2.1 t ht) (mul_nonneg ha (hn t))
  · filter_upwards [hρ.2.2.1, h0] with x hx hz
    simp only [hx, hz, mul_zero, add_zero]
  · filter_upwards [hρ.2.2.2, h1] with x hx hz
    simp only [hx, hz, mul_zero, add_zero]

end

end RepeatedIntegrals
