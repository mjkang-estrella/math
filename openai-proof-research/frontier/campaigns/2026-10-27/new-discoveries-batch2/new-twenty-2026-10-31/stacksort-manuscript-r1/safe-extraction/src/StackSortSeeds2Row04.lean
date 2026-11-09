import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_4_0 : ∀ s : Fin 5,
 (tableX 4 0 s, tableI 4 0 s) = topStep tableX tableI 4 0 s := by decide
theorem row_valid_4_1 : ∀ s : Fin 5,
 (tableX 4 1 s, tableI 4 1 s) = topStep tableX tableI 4 1 s := by decide
theorem row_valid_4_2 : ∀ s : Fin 5,
 (tableX 4 2 s, tableI 4 2 s) = topStep tableX tableI 4 2 s := by decide
theorem row_valid_4_3 : ∀ s : Fin 5,
 (tableX 4 3 s, tableI 4 3 s) = topStep tableX tableI 4 3 s := by decide
theorem row_valid_4_4 : ∀ s : Fin 5,
 (tableX 4 4 s, tableI 4 4 s) = topStep tableX tableI 4 4 s := by decide
theorem row_valid_4 : ∀ r s : Fin 5,
 (tableX 4 r s, tableI 4 r s) = topStep tableX tableI 4 r s := by
 intro r s
 fin_cases r
 · exact row_valid_4_0 s
 · exact row_valid_4_1 s
 · exact row_valid_4_2 s
 · exact row_valid_4_3 s
 · exact row_valid_4_4 s
end StackSort.Seeds2
