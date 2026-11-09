import ShoeProbability

namespace Shoe
open MeasureTheory

theorem winner_at_first {α : Type*} [Inhabited α] {ω : Sample α} {n : ℕ}
    (h : FirstMatch ω n) : winner ω = ω n := by
  classical
  have ht : Terminates ω := ⟨n+1, h.1⟩
  have hl : firstLength ω ht = n+1 := by
    apply Nat.le_antisymm
    · exact Nat.find_le h.1
    · by_contra hh
      have hm : firstLength ω ht ≤ n := by omega
      exact h.2 (hasMatch_mono hm (firstLength_spec ω ht))
  simp only [winner, dite_eq_left ht, hl, Nat.add_sub_cancel]

theorem first_at_least {α : Type*} (ω : Sample α) (h : Terminates ω) :
    FirstMatch ω (firstLength ω h - 1) := by
  have hp : 0 < firstLength ω h := by
    by_contra hn
    have hz : firstLength ω h = 0 := by omega
    have hm := firstLength_spec ω h
    rw [hz] at hm
    exact no_match_empty ω hm
  constructor
  · have he : firstLength ω h - 1 + 1 = firstLength ω h := by omega
    rw [he]
    exact firstLength_spec ω h
  · exact firstLength_min ω h (by omega)

theorem winner_fiber (i : ℕ) :
    {ω : Sample ℕ | winner ω = i} =
      ({ω | ¬ Terminates ω} ∩ {_ω | (default : ℕ) = i}) ∪
      ⋃ n : ℕ, ({ω | FirstMatch ω n} ∩ {ω | ω n = i}) := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · intro hi
    by_cases ht : Terminates ω
    · right
      refine ⟨firstLength ω ht - 1, first_at_least ω ht, ?_⟩
      simpa only [winner, dite_eq_left ht] using hi
    · left
      exact ⟨ht, by simpa only [winner, dite_eq_right ht] using hi⟩
  · rintro (⟨ht, hi⟩ | ⟨n, hn, hi⟩)
    · simpa only [winner, dite_eq_right ht] using hi
    · exact (winner_at_first hn).trans hi

theorem measurable_winner : Measurable (winner : Sample ℕ → ℕ) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {ω : Sample ℕ | winner ω = i}
  rw [winner_fiber]
  apply MeasurableSet.union
  · exact measurable_terminates.compl.inter (MeasurableSet.const _)
  · apply MeasurableSet.iUnion
    intro n
    exact (measurable_firstMatch n).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

/-- Genuine pushforward PMF. The fallback at nontermination is explicit;
the proof that its exceptional set has zero mass is a separate obligation. -/
noncomputable def winningLaw (p : DiscreteLaw ℕ) : PMF ℕ :=
  ((sampleMeasure p).map winner).toPMF

theorem winningLaw_apply (p : DiscreteLaw ℕ) (i : ℕ) :
    winningLaw p i = sampleMeasure p {ω | winner ω = i} := by
  unfold winningLaw
  rw [Measure.toPMF_apply, Measure.map_apply measurable_winner (measurableSet_singleton i)]
  rfl

end Shoe
