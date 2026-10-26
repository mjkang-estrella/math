import SortedBridge

open scoped BigOperators

namespace MaxIndex

theorem maskTopSum_reindex_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (f : β → ℝ) (k : ℕ) :
    maskTopSum (f ∘ e) k ≤ maskTopSum f k := by
  apply maskTopSum_le
  intro s hs
  have h := selected_sum_le_maskTopSum f k (s.map e.toEmbedding) (by simpa using hs)
  simpa using h

theorem maskTopSum_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (f : β → ℝ) (k : ℕ) :
    maskTopSum (f ∘ e) k = maskTopSum f k := by
  apply le_antisymm (maskTopSum_reindex_le e f k)
  have h := maskTopSum_reindex_le e.symm (f ∘ e) k
  simpa [Function.comp_def] using h

theorem sortedTopSum_mono {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) {k l : ℕ} (hkl : k ≤ l)
    (hl : l ≤ Fintype.card α) : sortedTopSum f k ≤ sortedTopSum f l := by
  rw [sortedTopSum_eq_maskTopSum f hf k (hkl.trans hl),
    sortedTopSum_eq_maskTopSum f hf l hl]
  exact maskTopSum_mono f hkl

end MaxIndex
