#!/bin/bash
set -eu
{
for n in $(seq -w 1 20); do echo "import StackSortSeeds2Row$n"; done
cat <<'LEAN'
import Mathlib.Tactic.IntervalCases
namespace StackSort.Seeds2
 theorem table_recursion : Recursion tableX tableI := by
  intro M r s
  by_cases hM : M = 0
  · subst M; simp [tableX, tableI, table, topStep]
  by_cases hB : 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M
  · have h20 : M ≤ 20 := by have := hB.2.1; unfold bound at this; omega
    have h1 : 1 ≤ M := by omega
    interval_cases M
LEAN
for n in $(seq 1 20); do echo "    · exact row_valid_$n ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩"; done
cat <<'LEAN'
  · simp [tableX, tableI, table, topStep, hM, hB]
end StackSort.Seeds2
LEAN
} > StackSortSeeds2Checked.lean
