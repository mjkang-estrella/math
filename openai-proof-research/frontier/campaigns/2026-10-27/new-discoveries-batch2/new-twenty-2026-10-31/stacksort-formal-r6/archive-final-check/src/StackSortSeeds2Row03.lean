import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_3_0 : ∀ s : Fin 4,
 (tableX 3 0 s, tableI 3 0 s) = topStep tableX tableI 3 0 s := by decide
theorem row_valid_3_1 : ∀ s : Fin 4,
 (tableX 3 1 s, tableI 3 1 s) = topStep tableX tableI 3 1 s := by decide
theorem row_valid_3_2 : ∀ s : Fin 4,
 (tableX 3 2 s, tableI 3 2 s) = topStep tableX tableI 3 2 s := by decide
theorem row_valid_3_3 : ∀ s : Fin 4,
 (tableX 3 3 s, tableI 3 3 s) = topStep tableX tableI 3 3 s := by decide
theorem row_valid_3 : ∀ r s : Fin 4,
 (tableX 3 r s, tableI 3 r s) = topStep tableX tableI 3 r s := by
 intro r s
 fin_cases r
 · exact row_valid_3_0 s
 · exact row_valid_3_1 s
 · exact row_valid_3_2 s
 · exact row_valid_3_3 s
end StackSort.Seeds2
