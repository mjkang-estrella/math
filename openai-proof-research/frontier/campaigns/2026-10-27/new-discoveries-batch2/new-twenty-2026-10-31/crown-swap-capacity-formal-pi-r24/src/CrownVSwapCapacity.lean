import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Capacity-only extraction of the r23 swap draft. Total-sum and strict-weight invariants remain unpaid. Only compiler-prescribed conditional lemma renames were applied by root. -/

namespace CrownV

/-- The allocation obtained from `a` by one legal swap `j → i`: the plain
function `a` with two ordinary function updates, `+1` at `i` and `-1` at `j`,
all other values left untouched. -/
def swapAlloc (a : Nat → Nat) (i j : Nat) : Nat → Nat :=
  Function.update (Function.update a i (a i + 1)) j (a j - 1)

/-- Pointwise reading of the two updates, in application order. -/
theorem swapAlloc_eval (a : Nat → Nat) (i j k : Nat) :
    swapAlloc a i j k = if k = j then a j - 1 else if k = i then a i + 1 else a k := by
  unfold swapAlloc
  rw [Function.update_apply, Function.update_apply]

/-- Value at the receiving column `k = i`: one unit gained. -/
theorem swapAlloc_at_i (a : Nat → Nat) (i j k : Nat) (hij : i < j) (h : k = i) :
    swapAlloc a i j k = a k + 1 := by
  have hne : i ≠ j := ne_of_lt hij
  rw [swapAlloc_eval, ite_eq_right (show k ≠ j from fun hh => hne (h.symm.trans hh)), ite_eq_left h, ← h]

/-- Value at the losing column `k = j`: one unit lost. -/
theorem swapAlloc_at_j (a : Nat → Nat) (i j k : Nat) (h : k = j) :
    swapAlloc a i j k = a k - 1 := by
  rw [swapAlloc_eval, ite_eq_left h, ← h]

/-- Value at any column distinct from both `i` and `j`: unchanged. -/
theorem swapAlloc_at_else (a : Nat → Nat) (i j k : Nat) (h1 : k ≠ i) (h2 : k ≠ j) :
    swapAlloc a i j k = a k := by
  rw [swapAlloc_eval, ite_eq_right h2, ite_eq_right h1]

/-- Prefix capacity preservation: if `a` respects the capacities `d` on the
prefix `k < m`, then so does the swapped allocation, in particular at the
receiving column `i` (where `a i < d i` opens room) and at the losing column
`j` (where removal only decreases).  No boundary exclusions. -/
theorem swapAlloc_capacity (m i j : Nat) (d a : Nat → Nat)
    (hij : i < j) (hjm : j < m) (hid : a i < d i)
    (hcap : ∀ k, k < m → a k ≤ d k) :
    ∀ k, k < m → swapAlloc a i j k ≤ d k := by
  intro k hk
  by_cases h1 : k = i
  · rw [swapAlloc_at_i a i j k hij h1]
    have hid' : a k < d k := by rw [h1]; exact hid
    omega
  · by_cases h2 : k = j
    · rw [swapAlloc_at_j a i j k h2]
      have hc : a k ≤ d k := by rw [h2]; exact hcap j hjm
      omega
    · rw [swapAlloc_at_else a i j k h1 h2]
      exact hcap k hk

end CrownV
