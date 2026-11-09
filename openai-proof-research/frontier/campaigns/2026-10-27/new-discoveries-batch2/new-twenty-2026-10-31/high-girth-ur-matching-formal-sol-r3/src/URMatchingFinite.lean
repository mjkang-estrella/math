module
public import URMatchingBase
@[expose] public section
namespace URMatching
universe u
variable {V : Type u} (G : SimpleGraph V)

@[simp] theorem empty_isMatching : IsMatching G ∅ := by
  simp [IsMatching]

@[simp] theorem covered_empty : Covered (∅ : Finset (Sym2 V)) = ∅ := by
  ext v
  simp [Covered]

theorem eq_empty_of_covered_empty (M : Finset (Sym2 V)) (h : Covered M = ∅) : M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
  have hv : x ∈ Covered M := ⟨s(x, y), he, Sym2.mem_mk_left x y⟩
  rw [h] at hv
  exact hv

@[simp] theorem empty_isUR : IsUR G ∅ := by
  refine ⟨empty_isMatching G, ?_⟩
  intro M _ hc
  exact eq_empty_of_covered_empty M (hc.trans covered_empty)

variable [Fintype V]

theorem card_le_matchingNumber {M : Finset (Sym2 V)} (h : IsMatching G M) :
    M.card ≤ matchingNumber G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem card_le_urMatchingNumber {M : Finset (Sym2 V)} (h : IsUR G M) :
    M.card ≤ urMatchingNumber G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem exists_maximum_matching : ∃ M : Finset (Sym2 V),
    IsMatching G M ∧ M.card = matchingNumber G := by
  classical
  let S := (Finset.univ : Finset (Finset (Sym2 V))).filter (IsMatching G)
  have hs : S.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty_isMatching G⟩⟩
  obtain ⟨M, hm, heq⟩ := Finset.exists_mem_eq_sup S hs Finset.card
  exact ⟨M, (Finset.mem_filter.mp hm).2, heq.symm⟩

theorem exists_maximum_urMatching : ∃ M : Finset (Sym2 V),
    IsUR G M ∧ M.card = urMatchingNumber G := by
  classical
  let S := (Finset.univ : Finset (Finset (Sym2 V))).filter (IsUR G)
  have hs : S.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty_isUR G⟩⟩
  obtain ⟨M, hm, heq⟩ := Finset.exists_mem_eq_sup S hs Finset.card
  exact ⟨M, (Finset.mem_filter.mp hm).2, heq.symm⟩

theorem urMatchingNumber_le_matchingNumber : urMatchingNumber G ≤ matchingNumber G := by
  obtain ⟨M, hm, heq⟩ := exists_maximum_urMatching G
  rw [← heq]
  exact card_le_matchingNumber G hm.1

/-- This exact universal characterization verifies that the supremum ranges over all matchings. -/
theorem matchingNumber_le_iff (k : ℕ) :
    matchingNumber G ≤ k ↔ ∀ M, IsMatching G M → M.card ≤ k := by
  classical
  constructor
  · intro h M hm; exact (card_le_matchingNumber G hm).trans h
  · intro h
    exact Finset.sup_le fun M hm => h M (Finset.mem_filter.mp hm).2

theorem urMatchingNumber_le_iff (k : ℕ) :
    urMatchingNumber G ≤ k ↔ ∀ M, IsUR G M → M.card ≤ k := by
  classical
  constructor
  · intro h M hm; exact (card_le_urMatchingNumber G hm).trans h
  · intro h
    exact Finset.sup_le fun M hm => h M (Finset.mem_filter.mp hm).2
end URMatching
