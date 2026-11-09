import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_5_0 : ∀ s : Fin 6,
 (tableX 5 0 s, tableI 5 0 s) = topStep tableX tableI 5 0 s := by decide
theorem row_valid_5_1 : ∀ s : Fin 6,
 (tableX 5 1 s, tableI 5 1 s) = topStep tableX tableI 5 1 s := by decide
theorem row_valid_5_2 : ∀ s : Fin 6,
 (tableX 5 2 s, tableI 5 2 s) = topStep tableX tableI 5 2 s := by decide
theorem row_valid_5_3 : ∀ s : Fin 6,
 (tableX 5 3 s, tableI 5 3 s) = topStep tableX tableI 5 3 s := by decide
theorem row_valid_5_4 : ∀ s : Fin 6,
 (tableX 5 4 s, tableI 5 4 s) = topStep tableX tableI 5 4 s := by decide
theorem row_valid_5_5 : ∀ s : Fin 6,
 (tableX 5 5 s, tableI 5 5 s) = topStep tableX tableI 5 5 s := by decide
theorem row_valid_5 : ∀ r s : Fin 6,
 (tableX 5 r s, tableI 5 r s) = topStep tableX tableI 5 r s := by
 intro r s
 fin_cases r
 · exact row_valid_5_0 s
 · exact row_valid_5_1 s
 · exact row_valid_5_2 s
 · exact row_valid_5_3 s
 · exact row_valid_5_4 s
 · exact row_valid_5_5 s
end StackSort.Seeds2
