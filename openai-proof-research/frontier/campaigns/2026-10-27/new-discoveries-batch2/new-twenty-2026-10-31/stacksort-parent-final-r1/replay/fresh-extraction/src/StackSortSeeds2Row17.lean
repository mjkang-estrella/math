import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_17_0 : ∀ s : Fin 5,
 (tableX 17 0 s, tableI 17 0 s) = topStep tableX tableI 17 0 s := by decide
theorem row_valid_17_1 : ∀ s : Fin 5,
 (tableX 17 1 s, tableI 17 1 s) = topStep tableX tableI 17 1 s := by decide
theorem row_valid_17_2 : ∀ s : Fin 5,
 (tableX 17 2 s, tableI 17 2 s) = topStep tableX tableI 17 2 s := by decide
theorem row_valid_17_3 : ∀ s : Fin 5,
 (tableX 17 3 s, tableI 17 3 s) = topStep tableX tableI 17 3 s := by decide
theorem row_valid_17_4 : ∀ s : Fin 5,
 (tableX 17 4 s, tableI 17 4 s) = topStep tableX tableI 17 4 s := by decide
theorem row_valid_17 : ∀ r s : Fin 5,
 (tableX 17 r s, tableI 17 r s) = topStep tableX tableI 17 r s := by
 intro r s
 fin_cases r
 · exact row_valid_17_0 s
 · exact row_valid_17_1 s
 · exact row_valid_17_2 s
 · exact row_valid_17_3 s
 · exact row_valid_17_4 s
end StackSort.Seeds2
