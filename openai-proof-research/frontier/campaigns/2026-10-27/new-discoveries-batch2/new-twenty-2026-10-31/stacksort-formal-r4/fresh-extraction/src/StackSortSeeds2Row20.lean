import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_20_0 : ∀ s : Fin 2,
 (tableX 20 0 s, tableI 20 0 s) = topStep tableX tableI 20 0 s := by decide
theorem row_valid_20_1 : ∀ s : Fin 2,
 (tableX 20 1 s, tableI 20 1 s) = topStep tableX tableI 20 1 s := by decide
theorem row_valid_20 : ∀ r s : Fin 2,
 (tableX 20 r s, tableI 20 r s) = topStep tableX tableI 20 r s := by
 intro r s
 fin_cases r
 · exact row_valid_20_0 s
 · exact row_valid_20_1 s
end StackSort.Seeds2
