import StackSortCut5Pieces

noncomputable section
namespace StackSort.Cut5
open Seeds2 Shuffle3 Round4 Classical BigOperators

theorem pieces_card_sum (M r s : ℕ) :
    (pieces M r s).card = ∑ b ∈ Finset.Ico 1 M, ∑ a ∈ Finset.Ico 1 r,
      ∑ c ∈ Finset.Ico 1 s, Nat.choose M b * (XI (M-b) (r-a) (s-c) * II b a c) := by
  simp only [pieces,Finset.card_sigma,Finset.card_product,labelledPairs_card,
    labelledIrreducibles_card,indices,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  have he : (∑ A ∈ (Finset.range M).powerset,
      if A.card = b then XI (Finset.range M \ A).card (r-a) (s-c) * II A.card a c else 0) =
      ∑ A ∈ (Finset.range M).powersetCard b, XI (M-b) (r-a) (s-c) * II b a c := by
    rw [Finset.powersetCard_eq_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases h : A.card = b
    · rw [ite_eq_left h,ite_eq_left h,h,Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA),Finset.card_range,h]
    · rw [ite_eq_right h,ite_eq_right h]
  rw [he]
  simp [Finset.card_powersetCard,Finset.card_range]

/-- Unclipped T1 for arbitrary positive size and arbitrary tuple arities. -/
theorem commonCutCount_raw (M r s : ℕ) (hM : 0 < M) :
    XI M r s = II M r s + ∑ b ∈ Finset.Ico 1 M, ∑ a ∈ Finset.Ico 1 r,
      ∑ c ∈ Finset.Ico 1 s, Nat.choose M b * (XI (M-b) (r-a) (s-c) * II b a c) := by
  rw [← pieces_card_sum, pieces_card M r s hM]
  exact XI_partition M r s

end StackSort.Cut5
