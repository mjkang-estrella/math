import Mathlib

/- The descending-index helpers are adapted from this campaign's already verified
MaxIndex.SortedBridge. They are standard infrastructure, not discovery credit.
The exact-cardinality/fractional-mass statements below allow negative entries. -/

open Finset

namespace ConnectionGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

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


noncomputable def topSet (f : α → ℝ) (k : ℕ) : Finset α :=
  ((descendingIndices f).take k).toFinset

theorem topSet_card (f : α → ℝ) {k : ℕ} (hk : k ≤ Fintype.card α) :
    (topSet f k).card = k := by
  rw [topSet, List.toFinset_card_of_nodup ((descendingIndices_nodup f).take),
    List.length_take, descendingIndices_length, Nat.min_eq_left hk]

theorem sortedTopSum_eq_sum_topSet (f : α → ℝ) (k : ℕ) :
    sortedTopSum f k = ∑ i ∈ topSet f k, f i := by
  exact (List.sum_toFinset _ ((descendingIndices_nodup f).take)).symm

theorem topSet_dominates (f : α → ℝ) (k : ℕ) {i j : α}
    (hi : i ∉ topSet f k) (hj : j ∈ topSet f k) : f i ≤ f j := by
  have himem : i ∈ descendingIndices f := descendingIndices_mem f i
  have hinot : i ∉ (descendingIndices f).take k := by simpa [topSet] using hi
  have hidrop : i ∈ (descendingIndices f).drop k := by
    have hboth : i ∈ (descendingIndices f).take k ∨ i ∈ (descendingIndices f).drop k := by
      rw [← List.mem_append, List.take_append_drop]
      exact himem
    exact hboth.resolve_left hinot
  have hjtake : j ∈ (descendingIndices f).take k := List.mem_toFinset.mp hj
  have hpair : ((descendingIndices f).take k ++ (descendingIndices f).drop k).Pairwise
      (fun a b => f b ≤ f a) := by
    rw [List.take_append_drop]
    exact descendingIndices_pairwise f
  exact (List.pairwise_append.mp hpair).2.2 j hjtake i hidrop

omit [Fintype α] in
theorem sum_le_top_equal_card (f : α → ℝ) (s t : Finset α) (hst : s.card = t.card)
    (ht : ∀ i, i ∉ t → ∀ j ∈ t, f i ≤ f j) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ t, f i := by
  classical
  by_cases ht0 : t.Nonempty
  · obtain ⟨u, hut, hu⟩ := exists_min_image t f ht0
    have hdiffcard : ((s \ t).card : ℝ) = (t \ s).card := by
      exact_mod_cast card_sdiff_comm hst
    have hleft : (∑ i ∈ s \ t, f i) ≤ (s \ t).card * f u := by
      calc
        _ ≤ ∑ _i ∈ s \ t, f u := sum_le_sum (fun i hi => ht i (mem_sdiff.mp hi).2 u hut)
        _ = _ := by simp
    have hright : (t \ s).card * f u ≤ ∑ i ∈ t \ s, f i := by
      calc
        _ = ∑ _i ∈ t \ s, f u := by simp
        _ ≤ _ := sum_le_sum (fun i hi => hu i (mem_sdiff.mp hi).1)
    have hs := sum_inter_add_sum_sdiff s t f
    have htt := sum_inter_add_sum_sdiff t s f
    rw [inter_comm t s] at htt
    rw [hdiffcard] at hleft
    linarith
  · have ht' : t = ∅ := not_nonempty_iff_eq_empty.mp ht0
    have hs' : s = ∅ := card_eq_zero.mp (by simpa [ht'] using hst)
    simp [hs', ht']

theorem selected_sum_le_sortedTopSum (f : α → ℝ) (s : Finset α) {k : ℕ}
    (hk : k ≤ Fintype.card α) (hs : s.card = k) :
    (∑ i ∈ s, f i) ≤ sortedTopSum f k := by
  rw [sortedTopSum_eq_sum_topSet]
  exact sum_le_top_equal_card f s (topSet f k) (hs.trans (topSet_card f hk).symm)
    (fun _ hi _ hj => topSet_dominates f k hi hj)

theorem sortedTopSum_le_of_selected (f : α → ℝ) {k : ℕ} (hk : k ≤ Fintype.card α)
    (b : ℝ) (hb : ∀ s : Finset α, s.card = k → (∑ i ∈ s, f i) ≤ b) :
    sortedTopSum f k ≤ b := by
  rw [sortedTopSum_eq_sum_topSet]
  exact hb _ (topSet_card f hk)

theorem fractional_sum_le_sortedTopSum (f w : α → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card α) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hmass : ∑ i, w i = k) : (∑ i, w i * f i) ≤ sortedTopSum f k := by
  classical
  by_cases hk0 : k = 0
  · have hw0 : ∀ i, w i = 0 := by
      intro i
      have hb := single_le_sum (fun j _ => (hw j).1) (mem_univ i)
      rw [hmass, hk0, Nat.cast_zero] at hb
      exact le_antisymm hb (hw i).1
    simp [hw0, sortedTopSum, hk0]
  let t := topSet f k
  have hcard : t.card = k := topSet_card f hk
  have ht : t.Nonempty := card_pos.mp (by omega)
  obtain ⟨u, hut, hu⟩ := exists_min_image t f ht
  have hsplitw := sum_inter_add_sum_sdiff (univ : Finset α) t w
  simp only [univ_inter] at hsplitw
  have hmass' : (∑ i ∈ univ \ t, w i) = ∑ i ∈ t, (1 - w i) := by
    rw [sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one, hcard]
    linarith
  have hlow : (∑ i ∈ univ \ t, w i * f i) ≤ (∑ i ∈ univ \ t, w i) * f u := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (topSet_dominates f k (mem_sdiff.mp hi).2 hut) (hw i).1
  have hhigh : (∑ i ∈ t, (1 - w i)) * f u ≤ ∑ i ∈ t, (1 - w i) * f i := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hu i hi) (sub_nonneg.mpr (hw i).2)
  have he : (∑ i ∈ t, (1 - w i) * f i) = (∑ i ∈ t, f i) - ∑ i ∈ t, w i * f i := by
    simp_rw [sub_mul, one_mul]
    rw [sum_sub_distrib]
  have hsplit := sum_inter_add_sum_sdiff (univ : Finset α) t (fun i => w i * f i)
  simp only [univ_inter] at hsplit
  rw [hmass'] at hlow
  rw [he] at hhigh
  rw [sortedTopSum_eq_sum_topSet]
  change (∑ i, w i * f i) ≤ ∑ i ∈ t, f i
  linarith

end ConnectionGraph
