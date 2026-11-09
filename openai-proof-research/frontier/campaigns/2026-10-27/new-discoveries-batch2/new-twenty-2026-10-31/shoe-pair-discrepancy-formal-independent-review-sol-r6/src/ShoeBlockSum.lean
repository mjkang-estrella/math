import ShoeCollision

namespace Shoe
open MeasureTheory
open scoped ENNReal

theorem measurable_isolated (K a b i : ℕ) :
    MeasurableSet {ω : Sample ℕ | Isolated ω K a b i} := by
  classical
  unfold Isolated
  measurability

theorem measurable_goodBlock (K a b i : ℕ) :
    MeasurableSet {ω : Sample ℕ | GoodBlock ω K a b i} := by
  classical
  unfold GoodBlock
  apply (measurable_isolated K a b i).inter
  change MeasurableSet {ω : Sample ℕ | ∀ c < K, ∀ d < K, c ≠ a → d ≠ b → ω (2*c) ≠ ω (2*d+1)}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter; intro c
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iInter; intro d
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iInter; intro _
  exact (measurableSet_eq_fun
    (measurable_pi_apply (2*c) : Measurable (fun ω : Sample ℕ => ω (2*c)))
    (measurable_pi_apply (2*d+1))).compl

/-- Actual disjoint-position events sum into the existing chronological winning PMF. -/
theorem goodBlock_sum_le_winning (p : DiscreteLaw ℕ) (K i : ℕ) :
    ∑ ab ∈ (Finset.range K).product (Finset.range K),
      sampleMeasure p {ω | GoodBlock ω K ab.1 ab.2 i} ≤ winningLaw p i := by
  classical
  let s := (Finset.range K).product (Finset.range K)
  let f := fun ab : ℕ × ℕ => {ω : Sample ℕ | GoodBlock ω K ab.1 ab.2 i}
  have hd : Set.PairwiseDisjoint (↑s) f := by
    intro ab _ cd _ hne
    apply Set.disjoint_left.mpr
    intro ω h₁ h₂
    have hu := isolated_positions_unique h₁.1 h₂.1
    exact hne (Prod.ext hu.1 hu.2)
  have hm : ∀ ab ∈ s, MeasurableSet (f ab) := by
    intro ab _
    exact measurable_goodBlock K ab.1 ab.2 i
  change (∑ ab ∈ s, sampleMeasure p (f ab)) ≤ _
  rw [← measure_biUnion_finset hd hm, winningLaw_apply]
  apply measure_mono
  intro ω hω
  simp only [Set.mem_iUnion] at hω
  obtain ⟨ab,_,h⟩ := hω
  exact winner_of_goodBlock h

end Shoe
