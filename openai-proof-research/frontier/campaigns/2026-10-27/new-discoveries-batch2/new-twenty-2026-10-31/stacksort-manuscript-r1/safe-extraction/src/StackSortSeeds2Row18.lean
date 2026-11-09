import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_18_0 : ∀ s : Fin 4,
 (tableX 18 0 s, tableI 18 0 s) = topStep tableX tableI 18 0 s := by decide
theorem row_valid_18_1 : ∀ s : Fin 4,
 (tableX 18 1 s, tableI 18 1 s) = topStep tableX tableI 18 1 s := by decide
theorem row_valid_18_2 : ∀ s : Fin 4,
 (tableX 18 2 s, tableI 18 2 s) = topStep tableX tableI 18 2 s := by decide
theorem row_valid_18_3 : ∀ s : Fin 4,
 (tableX 18 3 s, tableI 18 3 s) = topStep tableX tableI 18 3 s := by decide
theorem row_valid_18 : ∀ r s : Fin 4,
 (tableX 18 r s, tableI 18 r s) = topStep tableX tableI 18 r s := by
 intro r s
 fin_cases r
 · exact row_valid_18_0 s
 · exact row_valid_18_1 s
 · exact row_valid_18_2 s
 · exact row_valid_18_3 s
end StackSort.Seeds2
