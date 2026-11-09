import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_13_0 : ∀ s : Fin 9,
 (tableX 13 0 s, tableI 13 0 s) = topStep tableX tableI 13 0 s := by decide
theorem row_valid_13_1 : ∀ s : Fin 9,
 (tableX 13 1 s, tableI 13 1 s) = topStep tableX tableI 13 1 s := by decide
theorem row_valid_13_2 : ∀ s : Fin 9,
 (tableX 13 2 s, tableI 13 2 s) = topStep tableX tableI 13 2 s := by decide
theorem row_valid_13_3 : ∀ s : Fin 9,
 (tableX 13 3 s, tableI 13 3 s) = topStep tableX tableI 13 3 s := by decide
theorem row_valid_13_4 : ∀ s : Fin 9,
 (tableX 13 4 s, tableI 13 4 s) = topStep tableX tableI 13 4 s := by decide
theorem row_valid_13_5 : ∀ s : Fin 9,
 (tableX 13 5 s, tableI 13 5 s) = topStep tableX tableI 13 5 s := by decide
theorem row_valid_13_6 : ∀ s : Fin 9,
 (tableX 13 6 s, tableI 13 6 s) = topStep tableX tableI 13 6 s := by decide
theorem row_valid_13_7 : ∀ s : Fin 9,
 (tableX 13 7 s, tableI 13 7 s) = topStep tableX tableI 13 7 s := by decide
theorem row_valid_13_8 : ∀ s : Fin 9,
 (tableX 13 8 s, tableI 13 8 s) = topStep tableX tableI 13 8 s := by decide
theorem row_valid_13 : ∀ r s : Fin 9,
 (tableX 13 r s, tableI 13 r s) = topStep tableX tableI 13 r s := by
 intro r s
 fin_cases r
 · exact row_valid_13_0 s
 · exact row_valid_13_1 s
 · exact row_valid_13_2 s
 · exact row_valid_13_3 s
 · exact row_valid_13_4 s
 · exact row_valid_13_5 s
 · exact row_valid_13_6 s
 · exact row_valid_13_7 s
 · exact row_valid_13_8 s
end StackSort.Seeds2
