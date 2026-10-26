import FiniteSelections

open scoped BigOperators

namespace MaxIndex

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem selected_sum_sq_le_card (f : α → ℝ) (s : Finset α) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f

omit [DecidableEq α] in
theorem selected_sum_le_sqrt (f : α → ℝ) (s : Finset α) (k : ℕ)
    (hk : s.card ≤ k) (hunit : ∑ i, (f i) ^ 2 = 1) :
    (∑ i ∈ s, f i) ≤ Real.sqrt k := by
  have hsub : (∑ i ∈ s, (f i) ^ 2) ≤ 1 := by
    rw [← hunit]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (by intros; positivity)
  have hcs := selected_sum_sq_le_card f s
  have hcard : (s.card : ℝ) ≤ k := by exact_mod_cast hk
  have hsq := Real.sq_sqrt (show 0 ≤ (k : ℝ) by positivity)
  have hn := Real.sqrt_nonneg (k : ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hsub (show 0 ≤ (s.card : ℝ) by positivity)]

theorem maskTopSum_le_sqrt (f : α → ℝ) (k : ℕ)
    (hunit : ∑ i, (f i) ^ 2 = 1) : maskTopSum f k ≤ Real.sqrt k := by
  exact maskTopSum_le f k _ (fun s hs => selected_sum_le_sqrt f s k hs hunit)

theorem maskTopSum_le_head_sqrt (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hunit : ∑ i, (f i) ^ 2 = 1) (k : ℕ) (hk0 : 0 < k)
    (hk : k ≤ Fintype.card α) (u : α) (hu : ∀ i, f i ≤ f u) :
    maskTopSum f k ≤ f u + Real.sqrt ((k - 1 : ℕ) * (1 - (f u) ^ 2)) := by
  obtain ⟨s, hs, hus, he⟩ := exists_full_maskTopSum_containing f hf k hk0 hk u hu
  have hcard : (s.erase u).card = k - 1 := by
    rw [Finset.card_erase_of_mem hus, hs]
  have hsub : (∑ i ∈ s.erase u, (f i) ^ 2) ≤ 1 - (f u) ^ 2 := by
    have htotal : (∑ i ∈ s, (f i) ^ 2) ≤ 1 := by
      rw [← hunit]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (by intros; positivity)
    rw [← Finset.sum_erase_add _ _ hus] at htotal
    linarith
  have htail0 : 0 ≤ 1 - (f u) ^ 2 :=
    (Finset.sum_nonneg (fun i _ => sq_nonneg (f i))).trans hsub
  have hcs := selected_sum_sq_le_card f (s.erase u)
  rw [hcard] at hcs
  have hmul := mul_le_mul_of_nonneg_left hsub (show 0 ≤ ((k - 1 : ℕ) : ℝ) by positivity)
  have hsq := Real.sq_sqrt (mul_nonneg (show 0 ≤ ((k - 1 : ℕ) : ℝ) by positivity) htail0)
  have hn := Real.sqrt_nonneg (((k - 1 : ℕ) : ℝ) * (1 - (f u) ^ 2))
  have htail : (∑ i ∈ s.erase u, f i) ≤
      Real.sqrt (((k - 1 : ℕ) : ℝ) * (1 - (f u) ^ 2)) := by
    nlinarith
  rw [← he, ← Finset.sum_erase_add _ _ hus]
  linarith

end MaxIndex
