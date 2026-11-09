import StackSortSeeds2Row01
import StackSortSeeds2Row02
import StackSortSeeds2Row03
import StackSortSeeds2Row04
import StackSortSeeds2Row05
import StackSortSeeds2Row06
import StackSortSeeds2Row07
import StackSortSeeds2Row08
import StackSortSeeds2Row09
import StackSortSeeds2Row10
import StackSortSeeds2Row11
import StackSortSeeds2Row12
import StackSortSeeds2Row13
import StackSortSeeds2Row14
import StackSortSeeds2Row15
import StackSortSeeds2Row16
import StackSortSeeds2Row17
import StackSortSeeds2Row18
import StackSortSeeds2Row19
import StackSortSeeds2Row20
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
    · exact row_valid_1 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_2 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_3 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_4 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_5 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_6 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_7 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_8 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_9 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_10 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_11 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_12 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_13 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_14 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_15 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_16 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_17 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_18 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_19 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
    · exact row_valid_20 ⟨r, by simpa [bound] using Nat.lt_succ_of_le hB.2.1⟩ ⟨s, by simpa [bound] using Nat.lt_succ_of_le hB.2.2.2⟩
  · simp [tableX, tableI, table, topStep, hM, hB]
end StackSort.Seeds2
