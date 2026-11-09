module
public import URMatchingWeightedMoment
@[expose] public section
namespace URMatching
open scoped Classical
/-- Joint existence in the full space; neither desirable event is a premise. -/
theorem exists_joint_tuple (h : ℕ) : ∃ a : ℕ, 0 < a ∧ h ≤ a ∧
    ∃ σ : PermutationTuples (4*a) 100,
      100*witnessWeight (4*a) h σ < 4*a ∧
      (∀ A B : Finset (Fin (4*a)), A.card = a → B.card = a →
        ∃ c, ∃ x ∈ A, σ c x ∈ B) := by
  classical
  let a := h + 400*witnessBudget h + 1
  have ha : 0 < a := by omega
  have hh : h ≤ a := by omega
  have hb : 400*witnessBudget h < 4*a := by omega
  have hhole := strict_hole_estimate a ha
  have hheavy := heavy_event_strict a h ha hh hb
  let bad := holeEvent (4*a) a ∪ heavyEvent a h
  have hc : bad.card < Fintype.card (PermutationTuples (4*a) 100) := by
    have hu : bad.card ≤ (holeEvent (4*a) a).card + (heavyEvent a h).card :=
      Finset.card_union_le _ _
    omega
  have ex : ∃ σ, σ ∉ bad := by
    by_contra hn
    have hu : bad = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro σ
      by_contra hσ
      exact hn ⟨σ,hσ⟩
    rw [hu, Finset.card_univ] at hc
    exact (Nat.lt_irrefl _) hc
  obtain ⟨σ,hσ⟩ := ex
  have hnhole : σ ∉ holeEvent (4*a) a := fun hp => hσ (Finset.mem_union_left _ hp)
  have hnheavy : σ ∉ heavyEvent a h := fun hp => hσ (Finset.mem_union_right _ hp)
  refine ⟨a, ha, hh, σ, ?_, ?_⟩
  · by_contra hn
    apply hnheavy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  · intro A B hA hB
    by_contra hn
    apply hnhole
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨(A,B), hA,hB⟩, ?_⟩⟩
    intro c x hx hB'
    exact hn ⟨c,x,hx,hB'⟩
end URMatching
