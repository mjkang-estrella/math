import Mathlib

open scoped BigOperators

namespace MaxIndex

variable {α : Type*} [Fintype α] [DecidableEq α]

def selectionFamily (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Finset (Finset α) := Finset.univ.powerset.filter (fun s => s.card ≤ k)

theorem mem_selectionFamily (k : ℕ) (s : Finset α) :
    s ∈ selectionFamily α k ↔ s.card ≤ k := by
  simp [selectionFamily]

theorem selectionFamily_nonempty (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    (selectionFamily α k).Nonempty := by
  exact ⟨∅, (mem_selectionFamily k ∅).2 (by simp)⟩

/-- Maximum over masks of at most k distinct indices. For nonnegative arrays this is
the usual largest-k sum. The sorted-list bridge is proved separately. -/
noncomputable def maskTopSum (f : α → ℝ) (k : ℕ) : ℝ :=
  (selectionFamily α k).sup' (selectionFamily_nonempty α k) (fun s => ∑ i ∈ s, f i)

theorem selected_sum_le_maskTopSum (f : α → ℝ) (k : ℕ) (s : Finset α)
    (hs : s.card ≤ k) : (∑ i ∈ s, f i) ≤ maskTopSum f k := by
  exact Finset.le_sup' (fun t : Finset α => ∑ i ∈ t, f i)
    ((mem_selectionFamily k s).2 hs)

theorem maskTopSum_le (f : α → ℝ) (k : ℕ) (b : ℝ)
    (hb : ∀ s : Finset α, s.card ≤ k → (∑ i ∈ s, f i) ≤ b) :
    maskTopSum f k ≤ b := by
  exact Finset.sup'_le _ _ (fun s hs => hb s ((mem_selectionFamily k s).1 hs))

theorem maskTopSum_nonneg (f : α → ℝ) (k : ℕ) : 0 ≤ maskTopSum f k := by
  simpa using selected_sum_le_maskTopSum f k ∅ (by simp)

theorem exists_maskTopSum (f : α → ℝ) (k : ℕ) :
    ∃ s : Finset α, s.card ≤ k ∧ (∑ i ∈ s, f i) = maskTopSum f k := by
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup'
    (selectionFamily_nonempty α k) (fun s => ∑ i ∈ s, f i)
  exact ⟨s, (mem_selectionFamily k s).1 hs, he.symm⟩

theorem maskTopSum_mono (f : α → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    maskTopSum f k ≤ maskTopSum f l := by
  apply maskTopSum_le
  intro s hs
  exact selected_sum_le_maskTopSum f l s (hs.trans hkl)

theorem exists_full_maskTopSum (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk : k ≤ Fintype.card α) :
    ∃ s : Finset α, s.card = k ∧ (∑ i ∈ s, f i) = maskTopSum f k := by
  obtain ⟨s, hs, he⟩ := exists_maskTopSum f k
  obtain ⟨t, hst, _, htk⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s) hs (by simpa using hk)
  refine ⟨t, htk, le_antisymm (selected_sum_le_maskTopSum f k t htk.le) ?_⟩
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (by intros; exact hf _)

theorem exists_full_maskTopSum_containing (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ Fintype.card α) (u : α)
    (hu : ∀ i, f i ≤ f u) :
    ∃ s : Finset α, s.card = k ∧ u ∈ s ∧ (∑ i ∈ s, f i) = maskTopSum f k := by
  obtain ⟨s, hs, he⟩ := exists_full_maskTopSum f hf k hk
  by_cases hus : u ∈ s
  · exact ⟨s, hs, hus, he⟩
  obtain ⟨v, hvs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let t := insert u (s.erase v)
  have hut : u ∉ s.erase v := fun h => hus (Finset.mem_of_mem_erase h)
  have htk : t.card = k := by
    dsimp [t]
    rw [Finset.card_insert_of_notMem hut, Finset.card_erase_of_mem hvs]
    omega
  have hsum : (∑ i ∈ s, f i) ≤ ∑ i ∈ t, f i := by
    dsimp [t]
    rw [Finset.sum_insert hut, ← Finset.sum_erase_add _ _ hvs]
    linarith [hu v]
  refine ⟨t, htk, by simp [t], le_antisymm ?_ (he ▸ hsum)⟩
  exact selected_sum_le_maskTopSum f k t htk.le

end MaxIndex
