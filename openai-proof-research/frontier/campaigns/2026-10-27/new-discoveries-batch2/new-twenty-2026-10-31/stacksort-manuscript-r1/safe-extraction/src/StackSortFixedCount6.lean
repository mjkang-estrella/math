import StackSortFixed6
noncomputable section
namespace StackSort.Fixed6
open Seeds2 Round4 Cut5 Del5 Classical BigOperators

theorem fixedPieces_card_sum (M r s : ℕ) (hM : 0 < M) :
    (fixedPieces M r s).card = ∑ b ∈ Finset.Ico 1 M, ∑ a ∈ Finset.Ico 1 r,
      ∑ c ∈ Finset.Ico 1 s, Nat.choose (M-1) (b-1) * (XI (M-b) (r-a) (s-c) * II b a c) := by
  have he : fixedPieces M r s =
      ((indices M r s).filter (fun i => M-1 ∈ i.2.2.2)).sigma (fun i =>
        labelledPairs (Finset.range M \ i.2.2.2) (r-i.2.1) (s-i.2.2.1) ×ˢ
        labelledIrreducibles i.2.2.2 i.2.1 i.2.2.1) := by
    ext p
    simp [fixedPieces,pieces,and_assoc,and_comm]
  rw [he]
  simp only [Finset.card_sigma,Finset.card_product,labelledPairs_card,
    labelledIrreducibles_card,indices,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  have he' : (∑ A ∈ (Finset.range M).powerset,
      if A.card = b then
        (if M-1 ∈ A then XI (Finset.range M \ A).card (r-a) (s-c) * II A.card a c else 0)
      else 0) =
      ∑ A ∈ ((Finset.range M).powersetCard b).filter ({M-1} ⊆ ·),
        XI (M-b) (r-a) (s-c) * II b a c := by
    rw [Finset.sum_filter,Finset.powersetCard_eq_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases h : A.card = b
    · rw [ite_eq_left h,ite_eq_left h,h,Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA),Finset.card_range,h]
      simp
    · simp [h]
  rw [he']
  rw [Finset.sum_const,smul_eq_mul,
    Finset.card_filter_powersetCard_subset {M-1} (Finset.range M) b
      (by simpa using Finset.mem_range.mpr (show M-1 < M by omega))
      (by simp only [Finset.card_singleton]; exact (Finset.mem_Ico.mp hb).1)]
  simp

def maximumSet (M r s : ℕ) := (labelledPairs (Finset.range M) r s).filter (lastMax M)

theorem irreducible_last {M r s : ℕ} (hM : 0 < M) {p : Cut5.Pair}
    (hp : p ∈ labelledIrreducibles (Finset.range M) r s) : lastMax M p := by
  rcases mem_irreducibles.mp hp with ⟨hF,hG,he,hi⟩
  have ht := labelled_max_last hF hG (Finset.Subset.refl _) (Finset.mem_range.mpr (by omega)) he hi
  simpa [lastMax,labelled_length hF] using ht

theorem maximum_partition (M r s : ℕ) (hM : 0 < M) :
    (maximumSet M r s).card = II M r s + (fixedReducibles M r s).card := by
  have hi : (maximumSet M r s).filter (fun p => Irreducible p.1 p.2) =
      labelledIrreducibles (Finset.range M) r s := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hi⟩
      have hp' := mem_pairs.mp (Finset.mem_filter.mp hp).1
      exact mem_irreducibles.mpr ⟨hp'.1,hp'.2.1,hp'.2.2,hi⟩
    · intro hp
      have hp' := mem_irreducibles.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨mem_pairs.mpr ⟨hp'.1,hp'.2.1,hp'.2.2.1⟩,irreducible_last hM hp⟩,hp'.2.2.2⟩
  have hn : (maximumSet M r s).filter (fun p => ¬ Irreducible p.1 p.2) =
      fixedReducibles M r s := by
    ext p
    simp [maximumSet,fixedReducibles,reducibles,and_assoc,and_comm]
  have h := Finset.card_filter_add_card_filter_not (s := maximumSet M r s)
    (p := fun p => Irreducible p.1 p.2)
  rw [hi,hn,labelledIrreducibles_card,Finset.card_range] at h
  exact h.symm

theorem maximumSet_card (M r s : ℕ) (hM : 0 < M) :
    Nat.card (MaximumPairs (M-1) r s) = (maximumSet M r s).card := by
  have he : MaximumPairs (M-1) r s ≃ {p // p ∈ maximumSet M r s} :=
    Equiv.subtypeEquivRight (by
      intro p
      simp [maximumSet,labelledPairs_range,lastMax,show M-1+1=M by omega,and_assoc])
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr he

theorem correction_true_eq_raw (M r s : ℕ) (hr : 1 ≤ r) (hrB : r ≤ bound M)
    (_hs : 1 ≤ s) (hsB : s ≤ bound M) :
    correction true literalX literalI M r s =
      ∑ b ∈ Finset.Ico 1 M, ∑ a ∈ Finset.Ico 1 r, ∑ c ∈ Finset.Ico 1 s,
        Nat.choose (M-1) (b-1) * (XI (M-b) (r-a) (s-c) * II b a c) := by
  unfold correction convolution
  simp only [ite_true]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hb := Finset.mem_Ico.mp hb
  have ha := Finset.mem_Ico.mp ha
  have hc := Finset.mem_Ico.mp hc
  have hr21 : r ≤ 21-M := (Nat.le_min.mp hrB).2
  have hs21 : s ≤ 21-M := (Nat.le_min.mp hsB).2
  rw [Cut5.literalX_eq_XI (M-b) (r-a) (s-c) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    literalI_eq_II b a c (by omega) (by omega) (by omega) (by omega) (by omega)]

theorem fixedMaximumDecomposition_proved : FixedMaximumDecomposition := by
  intro M r s hM hr hrB hs hsB
  rw [maximumSet_card M r s hM,maximum_partition M r s hM,
    ← fixedPieces_card M r s hM,fixedPieces_card_sum M r s hM,
    literalI_eq_II M r s hM hr hs (Nat.le_min.mp hrB).2 (Nat.le_min.mp hsB).2,
    correction_true_eq_raw M r s hr hrB hs hsB]
end StackSort.Fixed6
#print axioms StackSort.Fixed6.fixedMaximumDecomposition_proved
