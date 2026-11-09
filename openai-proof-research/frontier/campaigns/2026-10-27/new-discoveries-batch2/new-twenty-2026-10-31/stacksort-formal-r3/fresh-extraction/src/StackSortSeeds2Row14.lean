import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_14_0 : ∀ s : Fin 8,
 (tableX 14 0 s, tableI 14 0 s) = topStep tableX tableI 14 0 s := by decide
theorem row_valid_14_1 : ∀ s : Fin 8,
 (tableX 14 1 s, tableI 14 1 s) = topStep tableX tableI 14 1 s := by decide
theorem row_valid_14_2 : ∀ s : Fin 8,
 (tableX 14 2 s, tableI 14 2 s) = topStep tableX tableI 14 2 s := by decide
theorem row_valid_14_3 : ∀ s : Fin 8,
 (tableX 14 3 s, tableI 14 3 s) = topStep tableX tableI 14 3 s := by decide
theorem row_valid_14_4 : ∀ s : Fin 8,
 (tableX 14 4 s, tableI 14 4 s) = topStep tableX tableI 14 4 s := by decide
theorem row_valid_14_5 : ∀ s : Fin 8,
 (tableX 14 5 s, tableI 14 5 s) = topStep tableX tableI 14 5 s := by decide
theorem row_valid_14_6 : ∀ s : Fin 8,
 (tableX 14 6 s, tableI 14 6 s) = topStep tableX tableI 14 6 s := by decide
theorem row_valid_14_7 : ∀ s : Fin 8,
 (tableX 14 7 s, tableI 14 7 s) = topStep tableX tableI 14 7 s := by decide
theorem row_valid_14 : ∀ r s : Fin 8,
 (tableX 14 r s, tableI 14 r s) = topStep tableX tableI 14 r s := by
 intro r s
 fin_cases r
 · exact row_valid_14_0 s
 · exact row_valid_14_1 s
 · exact row_valid_14_2 s
 · exact row_valid_14_3 s
 · exact row_valid_14_4 s
 · exact row_valid_14_5 s
 · exact row_valid_14_6 s
 · exact row_valid_14_7 s
end StackSort.Seeds2
