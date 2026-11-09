import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_8_0 : ∀ s : Fin 9,
 (tableX 8 0 s, tableI 8 0 s) = topStep tableX tableI 8 0 s := by decide
theorem row_valid_8_1 : ∀ s : Fin 9,
 (tableX 8 1 s, tableI 8 1 s) = topStep tableX tableI 8 1 s := by decide
theorem row_valid_8_2 : ∀ s : Fin 9,
 (tableX 8 2 s, tableI 8 2 s) = topStep tableX tableI 8 2 s := by decide
theorem row_valid_8_3 : ∀ s : Fin 9,
 (tableX 8 3 s, tableI 8 3 s) = topStep tableX tableI 8 3 s := by decide
theorem row_valid_8_4 : ∀ s : Fin 9,
 (tableX 8 4 s, tableI 8 4 s) = topStep tableX tableI 8 4 s := by decide
theorem row_valid_8_5 : ∀ s : Fin 9,
 (tableX 8 5 s, tableI 8 5 s) = topStep tableX tableI 8 5 s := by decide
theorem row_valid_8_6 : ∀ s : Fin 9,
 (tableX 8 6 s, tableI 8 6 s) = topStep tableX tableI 8 6 s := by decide
theorem row_valid_8_7 : ∀ s : Fin 9,
 (tableX 8 7 s, tableI 8 7 s) = topStep tableX tableI 8 7 s := by decide
theorem row_valid_8_8 : ∀ s : Fin 9,
 (tableX 8 8 s, tableI 8 8 s) = topStep tableX tableI 8 8 s := by decide
theorem row_valid_8 : ∀ r s : Fin 9,
 (tableX 8 r s, tableI 8 r s) = topStep tableX tableI 8 r s := by
 intro r s
 fin_cases r
 · exact row_valid_8_0 s
 · exact row_valid_8_1 s
 · exact row_valid_8_2 s
 · exact row_valid_8_3 s
 · exact row_valid_8_4 s
 · exact row_valid_8_5 s
 · exact row_valid_8_6 s
 · exact row_valid_8_7 s
 · exact row_valid_8_8 s
end StackSort.Seeds2
