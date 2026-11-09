import StackSortDel5Bijection
namespace StackSort.Del5
open Seeds2 Round4

theorem tuple_length_le_flatten {F : List (List ℕ)} (hn : NonemptyWords F) :
    F.length ≤ F.flatten.length := by
  induction F with
  | nil => simp
  | cons w F ih =>
    have hw : 0 < w.length := List.length_pos_iff.mpr (hn w (by simp))
    have hF := ih (fun v hv => hn v (by simp [hv]))
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

theorem tuple_supported {M r : ℕ} {F : List (List ℕ)} (h : F ∈ tuples M r) :
    r ≤ M ∧ (r = 0 ↔ M = 0) := by
  obtain ⟨hw,hl,hn⟩ := mem_tuples.mp h
  have hp := (mem_words.mp hw).length_eq
  simp only [List.length_range] at hp
  have hb := tuple_length_le_flatten hn
  refine ⟨by omega,?_⟩
  constructor
  · intro hr
    have he : F = [] := List.length_eq_zero_iff.mp (hl.trans hr)
    simp [he] at hp
    omega
  · intro hM; omega

theorem tuples_empty_of_unsupported (M r : ℕ)
    (h : M < r ∨ (r = 0 ∧ M ≠ 0)) : tuples M r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F hF
  have hs := tuple_supported hF
  rcases h with h | ⟨hr,hM⟩
  · omega
  · exact hM (hs.2.mp hr)

/-- Within the retained diagonal, clipping is exactly the raw literal count. -/
theorem literalX_eq_XI (M r s : ℕ) (hr : r ≤ 21-M) (hs : s ≤ 21-M) :
    literalX M r s = XI M r s := by
  classical
  by_cases hM : M = 0
  · subst M
    have ht : ∀ k, tuples 0 k = if k = 0 then {[]} else ∅ := by
      intro k
      split_ifs with hk
      · subst k
        ext F
        rw [mem_tuples]
        simp only [Finset.mem_singleton]
        constructor
        · intro h; exact List.length_eq_zero_iff.mp h.2.1
        · rintro rfl; simp [mem_words]
      · exact tuples_empty_of_unsupported 0 k (Or.inl (by omega))
    by_cases hr0 : r = 0 <;> by_cases hs0 : s = 0 <;>
      simp [literalX,XI,ht,output,hr0,hs0,Finset.filter_singleton]
  by_cases hr0 : r = 0
  · have he := tuples_empty_of_unsupported M r (Or.inr ⟨hr0,hM⟩)
    have hz : XI M r s = 0 := by simp [XI,he]
    rw [hz]
    simp [literalX,hr0,hM]
  by_cases hs0 : s = 0
  · rw [show XI M r s = 0 by
      simp [XI,tuples_empty_of_unsupported M s (Or.inr ⟨hs0,hM⟩)]]
    simp [literalX,hs0,hM]
  by_cases hrM : r ≤ M
  · by_cases hsM : s ≤ M
    · have hrB : r ≤ bound M := by unfold bound; omega
      have hsB : s ≤ bound M := by unfold bound; omega
      simp [literalX,hM,show 1 ≤ r by omega,show 1 ≤ s by omega,hrB,hsB]
    · have he := tuples_empty_of_unsupported M s (Or.inl (by omega))
      have hsB : ¬ s ≤ bound M := by unfold bound; omega
      simp [literalX,XI,he,hM,hsB]
  · have he := tuples_empty_of_unsupported M r (Or.inl (by omega))
    have hrB : ¬ r ≤ bound M := by unfold bound; omega
    simp [literalX,XI,he,hM,hrB]

/-- All nine deletion terms stay in the retained diagonal. -/
theorem deletion_eq_raw (M r s : ℕ) (hM : 1 ≤ M)
    (hr0 : 1 ≤ r) (hs0 : 1 ≤ s)
    (hr : r ≤ bound M) (hs : s ≤ bound M) :
    deletion literalX M r s = deletion XI M r s := by
  unfold deletion
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  have ht := Finset.mem_range.mp ht
  have hu := Finset.mem_range.mp hu
  have hr' : r ≤ 21-M := (Nat.le_min.mp hr).2
  have hs' : s ≤ 21-M := (Nat.le_min.mp hs).2
  rw [literalX_eq_XI (M-1) (r-1+t) (s-1+u) (by omega) (by omega)]
end StackSort.Del5
