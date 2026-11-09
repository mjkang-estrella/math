from pathlib import Path
lane=Path(__file__).resolve().parent.parent
s='''import StackSortInj2Rows5
import Mathlib.Tactic.IntervalCases
namespace StackSort
open BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem lowerTable_seed_check : ∀ n : Fin 21, tableValue n = seed20[n.val]! := by decide
theorem lowerTable_step {n : ℕ} (h : 20 < n) (hn : n ≤ 130) :
    tableValue n = rootRhs tableValue n := by
  rw [rootRhs_eq_evalRhs tableValue (by omega)]
  interval_cases n
'''
for n in range(21,131):s+=f'  · exact lower_row_{n}\n'
s+='''
theorem G_eq_table {n : ℕ} (hn : n ≤ 130) : G n = tableValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 20
    · rw [G_seed hs]
      exact (lowerTable_seed_check ⟨n, by omega⟩).symm
    · rw [G_step (by omega), lowerTable_step (by omega) hn]
      unfold rootRhs
      rw [ih (n-1) (by omega) (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [ih i (by omega) (by omega), ih (n-1-i) (by omega) (by omega)]

theorem G_130_eq_lower130 : G 130 = lower130 := by
  rw [G_eq_table (by decide)]
  rfl

/-- Linkage is closed; the remaining input is the combinatorial RootSplit bound. -/
theorem lower130_of_seeds (hr : RootSplit) : ExactSeeds20 → Lower130 := by
  intro hs
  unfold Lower130
  rw [← G_130_eq_lower130]
  exact G_le_P hr hs 130
end StackSort
'''
(lane/'StackSortInj2Linkage.lean').write_text(s)
