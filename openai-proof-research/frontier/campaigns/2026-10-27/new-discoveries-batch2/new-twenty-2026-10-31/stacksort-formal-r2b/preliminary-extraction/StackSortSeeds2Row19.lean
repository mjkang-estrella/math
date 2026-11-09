import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_19_0 : ∀ s : Fin 3,
 (tableX 19 0 s, tableI 19 0 s) = topStep tableX tableI 19 0 s := by decide
theorem row_valid_19_1 : ∀ s : Fin 3,
 (tableX 19 1 s, tableI 19 1 s) = topStep tableX tableI 19 1 s := by decide
theorem row_valid_19_2 : ∀ s : Fin 3,
 (tableX 19 2 s, tableI 19 2 s) = topStep tableX tableI 19 2 s := by decide
theorem row_valid_19 : ∀ r s : Fin 3,
 (tableX 19 r s, tableI 19 r s) = topStep tableX tableI 19 r s := by
 intro r s
 fin_cases r
 · exact row_valid_19_0 s
 · exact row_valid_19_1 s
 · exact row_valid_19_2 s
end StackSort.Seeds2
