import FiniteSelections

open scoped BigOperators

namespace MaxIndex

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem sum_le_top_selection (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (s t : Finset α) (hst : s.card ≤ t.card)
    (ht : ∀ i, i ∉ t → ∀ j ∈ t, f i ≤ f j) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ t, f i := by
  classical
  by_cases ht0 : t.Nonempty
  · obtain ⟨u, hut, hu⟩ := Finset.exists_min_image t f ht0
    have hdiffcard : ((s \ t).card : ℝ) ≤ (t \ s).card := by
      exact_mod_cast Finset.card_sdiff_le_card_sdiff_iff.mpr hst
    have hleft : (∑ i ∈ s \ t, f i) ≤ (s \ t).card * f u := by
      calc
        _ ≤ ∑ _i ∈ s \ t, f u := Finset.sum_le_sum (fun i hi =>
          ht i (Finset.mem_sdiff.mp hi).2 u hut)
        _ = _ := by simp
    have hright : (t \ s).card * f u ≤ ∑ i ∈ t \ s, f i := by
      calc
        _ = ∑ _i ∈ t \ s, f u := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i hi => hu i (Finset.mem_sdiff.mp hi).1)
    have hmiddle := mul_le_mul_of_nonneg_right hdiffcard (hf u)
    have hs := Finset.sum_inter_add_sum_sdiff s t f
    have htt := Finset.sum_inter_add_sum_sdiff t s f
    rw [Finset.inter_comm t s] at htt
    linarith
  · have ht' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht0
    have hs' : s = ∅ := Finset.card_eq_zero.mp (by simpa [ht'] using hst)
    simp [hs', ht']

noncomputable def descendingIndices (f : α → ℝ) : List α :=
  Finset.univ.toList.mergeSort (fun i j => decide (f i ≥ f j))

omit [DecidableEq α] in
theorem descendingIndices_perm (f : α → ℝ) :
    (descendingIndices f).Perm Finset.univ.toList :=
  List.mergeSort_perm _ _

omit [DecidableEq α] in
theorem descendingIndices_nodup (f : α → ℝ) : (descendingIndices f).Nodup :=
  (descendingIndices_perm f).nodup_iff.mpr (Finset.nodup_toList _)

omit [DecidableEq α] in
theorem descendingIndices_mem (f : α → ℝ) (i : α) : i ∈ descendingIndices f := by
  rw [(descendingIndices_perm f).mem_iff]
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

omit [DecidableEq α] in
theorem descendingIndices_length (f : α → ℝ) :
    (descendingIndices f).length = Fintype.card α := by
  rw [(descendingIndices_perm f).length_eq]
  simp

omit [DecidableEq α] in
theorem descendingIndices_pairwise (f : α → ℝ) :
    (descendingIndices f).Pairwise (fun i j => f j ≤ f i) := by
  have h := List.pairwise_mergeSort (le := fun i j => decide (f i ≥ f j))
    (fun a b c hab hbc => by
      simpa only [decide_eq_true_eq] using
        (le_trans (show f c ≤ f b by simpa using hbc) (show f b ≤ f a by simpa using hab)))
    (fun a b => by simpa using le_total (f b) (f a)) Finset.univ.toList
  simpa only [descendingIndices, decide_eq_true_eq] using h

/-- Literal sum of the first k entries after ordering the index array by its value.
Equal values retain their multiplicities and do not affect the sum. -/
noncomputable def sortedTopSum (f : α → ℝ) (k : ℕ) : ℝ :=
  (((descendingIndices f).take k).map f).sum

theorem sortedTopSum_eq_maskTopSum (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk : k ≤ Fintype.card α) : sortedTopSum f k = maskTopSum f k := by
  classical
  let l := descendingIndices f
  let t := (l.take k).toFinset
  have hn : (l.take k).Nodup := (descendingIndices_nodup f).take
  have hcard : t.card = k := by
    rw [List.toFinset_card_of_nodup hn, List.length_take, descendingIndices_length,
      Nat.min_eq_left hk]
  have hsum : sortedTopSum f k = ∑ i ∈ t, f i := by
    exact (List.sum_toFinset _ hn).symm
  rw [hsum]
  apply le_antisymm (selected_sum_le_maskTopSum f k t hcard.le)
  apply maskTopSum_le
  intro s hs
  apply sum_le_top_selection f hf s t (hs.trans_eq hcard.symm)
  intro i hi j hj
  have himem : i ∈ l := descendingIndices_mem f i
  have hinot : i ∉ l.take k := by simpa only [t, List.mem_toFinset] using hi
  have hidrop : i ∈ l.drop k := by
    have hboth : i ∈ l.take k ∨ i ∈ l.drop k := by
      rw [← List.mem_append, List.take_append_drop]
      exact himem
    exact hboth.resolve_left hinot
  have hjtake : j ∈ l.take k := List.mem_toFinset.mp hj
  have hpair : (l.take k ++ l.drop k).Pairwise (fun a b => f b ≤ f a) := by
    rw [List.take_append_drop]
    exact descendingIndices_pairwise f
  exact (List.pairwise_append.mp hpair).2.2 j hjtake i hidrop

end MaxIndex
