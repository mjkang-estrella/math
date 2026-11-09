import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_15_0 : ∀ s : Fin 7,
 (tableX 15 0 s, tableI 15 0 s) = topStep tableX tableI 15 0 s := by decide
theorem row_valid_15_1 : ∀ s : Fin 7,
 (tableX 15 1 s, tableI 15 1 s) = topStep tableX tableI 15 1 s := by decide
theorem row_valid_15_2 : ∀ s : Fin 7,
 (tableX 15 2 s, tableI 15 2 s) = topStep tableX tableI 15 2 s := by decide
theorem row_valid_15_3 : ∀ s : Fin 7,
 (tableX 15 3 s, tableI 15 3 s) = topStep tableX tableI 15 3 s := by decide
theorem row_valid_15_4 : ∀ s : Fin 7,
 (tableX 15 4 s, tableI 15 4 s) = topStep tableX tableI 15 4 s := by decide
theorem row_valid_15_5 : ∀ s : Fin 7,
 (tableX 15 5 s, tableI 15 5 s) = topStep tableX tableI 15 5 s := by decide
theorem row_valid_15_6 : ∀ s : Fin 7,
 (tableX 15 6 s, tableI 15 6 s) = topStep tableX tableI 15 6 s := by decide
theorem row_valid_15 : ∀ r s : Fin 7,
 (tableX 15 r s, tableI 15 r s) = topStep tableX tableI 15 r s := by
 intro r s
 fin_cases r
 · exact row_valid_15_0 s
 · exact row_valid_15_1 s
 · exact row_valid_15_2 s
 · exact row_valid_15_3 s
 · exact row_valid_15_4 s
 · exact row_valid_15_5 s
 · exact row_valid_15_6 s
end StackSort.Seeds2
