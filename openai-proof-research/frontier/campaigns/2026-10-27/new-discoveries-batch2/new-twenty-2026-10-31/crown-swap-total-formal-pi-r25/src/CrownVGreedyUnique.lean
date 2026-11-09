import CrownVGreedyPrefix
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# CrownV greedy terminal uniqueness

Terminal-allocation uniqueness for the greedy scheme on an arbitrary capacity
sequence `d : Nat → Nat` over the finite prefix `i < m`.  If `a` is any
allocation such that

* `a i ≤ d i` for every `i < m` (capacity),
* `∑_{i<m} a i = r` (total budget exactly `r`),
* for all `i < j < m`, `a i < d i` implies `a j = 0` (once a column is
  underfull, every later column is empty),

then `a i = greedyStep d r i = min (d i) (r - ∑_{k<i} d k)` for every `i < m`.
No convergence, degree bounds, enumeration or saturation side conditions:
`m = 0`, singleton, zero capacities, `r = 0` and full saturation are all
covered by the single universal argument.
-/

namespace CrownV

/-- Terminal uniqueness: the capacity/budget/terminal-segment conditions force
the allocation to agree with `greedyStep` on every column `< m`. -/
theorem greedy_terminal_unique (m r : Nat) (d a : Nat → Nat)
    (h1 : ∀ i, i < m → a i ≤ d i)
    (h2 : ∑ i ∈ Finset.range m, a i = r)
    (h3 : ∀ i j, i < j → j < m → a i < d i → a j = 0) :
    ∀ i, i < m → a i = greedyStep d r i := by
  intro i him
  have hmem : ∀ k, k < i → k < m := fun k hk => lt_trans hk him
  have hui : a i ≤ d i := h1 i him
  -- pointwise domination of the prefix allocation by the prefix capacity
  have hle : ∑ k ∈ Finset.range i, a k ≤ ∑ k ∈ Finset.range i, d k :=
    Finset.sum_le_sum fun k hk => h1 k (hmem k (Finset.mem_range.mp hk))
  have hsplit : ∑ k ∈ Finset.range (i + 1), a k = ∑ k ∈ Finset.range i, a k + a i :=
    Finset.sum_range_succ a i
  -- Budget bound: `a i` never exceeds the residual budget after column `i`.
  have hu2 : a i ≤ r - ∑ k ∈ Finset.range i, d k := by
    by_cases hex : ∃ k, k < i ∧ a k < d k
    · obtain ⟨k, hklt, hkd⟩ := hex
      have hzero : a i = 0 := h3 k i hklt him hkd
      omega
    · -- no underfull earlier column: prefix allocation equals prefix capacity
      have heq : ∀ k, k < i → a k = d k := fun k hk =>
        le_antisymm (h1 k (hmem k hk)) (le_of_not_gt fun hlt => hex ⟨k, hk, hlt⟩)
      have hsum : ∑ k ∈ Finset.range i, a k = ∑ k ∈ Finset.range i, d k :=
        Finset.sum_congr rfl fun k hk => heq k (Finset.mem_range.mp hk)
      have hcap : ∑ k ∈ Finset.range i, d k + a i ≤ r := by
        rw [← hsum, ← hsplit, ← h2]
        exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      omega
  -- Once column `i` is underfull, all later columns are empty, so the whole
  -- allocation `r` already sits inside columns `≤ i`.
  have hl : min (d i) (r - ∑ k ∈ Finset.range i, d k) ≤ a i := by
    by_cases hlt : a i < d i
    · have htail : ∑ k ∈ Finset.range (i + 1), a k = ∑ k ∈ Finset.range m, a k :=
        Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hnot => by
          have hk1 : ¬ (k < i + 1) := fun hc => hnot (Finset.mem_range.2 hc)
          exact h3 i k (by omega) (Finset.mem_range.mp hk) hlt
      have hr : r ≤ ∑ k ∈ Finset.range i, d k + a i := by
        rw [← h2, ← htail, hsplit]
        omega
      omega
    · exact le_trans (min_le_left _ _) (le_of_not_gt hlt)
  show a i = min (d i) (r - ∑ k ∈ Finset.range i, d k)
  exact le_antisymm (by omega) hl

end CrownV
