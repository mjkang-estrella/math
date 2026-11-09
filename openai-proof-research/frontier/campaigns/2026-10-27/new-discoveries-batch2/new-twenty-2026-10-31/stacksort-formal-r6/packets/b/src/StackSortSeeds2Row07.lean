import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_7_0 : ∀ s : Fin 8,
 (tableX 7 0 s, tableI 7 0 s) = topStep tableX tableI 7 0 s := by decide
theorem row_valid_7_1 : ∀ s : Fin 8,
 (tableX 7 1 s, tableI 7 1 s) = topStep tableX tableI 7 1 s := by decide
theorem row_valid_7_2 : ∀ s : Fin 8,
 (tableX 7 2 s, tableI 7 2 s) = topStep tableX tableI 7 2 s := by decide
theorem row_valid_7_3 : ∀ s : Fin 8,
 (tableX 7 3 s, tableI 7 3 s) = topStep tableX tableI 7 3 s := by decide
theorem row_valid_7_4 : ∀ s : Fin 8,
 (tableX 7 4 s, tableI 7 4 s) = topStep tableX tableI 7 4 s := by decide
theorem row_valid_7_5 : ∀ s : Fin 8,
 (tableX 7 5 s, tableI 7 5 s) = topStep tableX tableI 7 5 s := by decide
theorem row_valid_7_6 : ∀ s : Fin 8,
 (tableX 7 6 s, tableI 7 6 s) = topStep tableX tableI 7 6 s := by decide
theorem row_valid_7_7 : ∀ s : Fin 8,
 (tableX 7 7 s, tableI 7 7 s) = topStep tableX tableI 7 7 s := by decide
theorem row_valid_7 : ∀ r s : Fin 8,
 (tableX 7 r s, tableI 7 r s) = topStep tableX tableI 7 r s := by
 intro r s
 fin_cases r
 · exact row_valid_7_0 s
 · exact row_valid_7_1 s
 · exact row_valid_7_2 s
 · exact row_valid_7_3 s
 · exact row_valid_7_4 s
 · exact row_valid_7_5 s
 · exact row_valid_7_6 s
 · exact row_valid_7_7 s
end StackSort.Seeds2
