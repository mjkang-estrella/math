import PolynomialConvexity.Factored

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

theorem lifetime_ne_ae {n L : ℕ} (hL : 0 < L) (e : Edge n L) (t : ℝ) :
    ∀ᵐ ω ∂clockMeasure n, lifetime hL e ω ≠ t := by
  have h : ∀ᵐ ω ∂clockMeasure n, ∀ v, ω v ≠ t := by
    rw [ae_all_iff]
    intro v
    exact Measure.ae_eval_ne (fun _ : Fin n => expMeasure 1) v t
  filter_upwards [h] with ω hω
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' (edge_nonempty hL e) ω
  exact fun heq => hω v (hv.symm.trans heq)

theorem joint_strict_weak_ae {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (t : Fin d → ℝ) :
    {ω | ∀ i, t i < lifetime hL (e i) ω} =ᵐ[clockMeasure n]
      {ω | ∀ i, t i ≤ lifetime hL (e i) ω} := by
  have h : ∀ᵐ ω ∂clockMeasure n, ∀ i, lifetime hL (e i) ω ≠ t i :=
    ae_all_iff.mpr (fun i => lifetime_ne_ae hL (e i) (t i))
  filter_upwards [h] with ω hω
  apply propext
  exact forall_congr' (fun i => lt_iff_le_and_ne.trans
    (and_iff_left (Ne.symm (hω i))))

theorem joint_strict_survival {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (t : Fin d → ℝ) :
    clockMeasure n {ω | ∀ i, t i < lifetime hL (e i) ω} =
      ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v)) := by
  rw [measure_congr (joint_strict_weak_ae hL e t)]
  exact joint_survival hL e t

theorem volume_coordinates_nonzero (d : ℕ) :
    ∀ᵐ t : Fin d → ℝ ∂volume, ∀ i, t i ≠ 0 := by
  rw [volume_pi, ae_all_iff]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i 0

end
end PolynomialConvexity
