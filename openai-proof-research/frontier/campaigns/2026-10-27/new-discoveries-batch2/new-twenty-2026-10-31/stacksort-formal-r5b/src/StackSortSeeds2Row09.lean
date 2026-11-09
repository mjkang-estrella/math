import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_9_0 : ∀ s : Fin 10,
 (tableX 9 0 s, tableI 9 0 s) = topStep tableX tableI 9 0 s := by decide
theorem row_valid_9_1 : ∀ s : Fin 10,
 (tableX 9 1 s, tableI 9 1 s) = topStep tableX tableI 9 1 s := by decide
theorem row_valid_9_2 : ∀ s : Fin 10,
 (tableX 9 2 s, tableI 9 2 s) = topStep tableX tableI 9 2 s := by decide
theorem row_valid_9_3 : ∀ s : Fin 10,
 (tableX 9 3 s, tableI 9 3 s) = topStep tableX tableI 9 3 s := by decide
theorem row_valid_9_4 : ∀ s : Fin 10,
 (tableX 9 4 s, tableI 9 4 s) = topStep tableX tableI 9 4 s := by decide
theorem row_valid_9_5 : ∀ s : Fin 10,
 (tableX 9 5 s, tableI 9 5 s) = topStep tableX tableI 9 5 s := by decide
theorem row_valid_9_6 : ∀ s : Fin 10,
 (tableX 9 6 s, tableI 9 6 s) = topStep tableX tableI 9 6 s := by decide
theorem row_valid_9_7 : ∀ s : Fin 10,
 (tableX 9 7 s, tableI 9 7 s) = topStep tableX tableI 9 7 s := by decide
theorem row_valid_9_8 : ∀ s : Fin 10,
 (tableX 9 8 s, tableI 9 8 s) = topStep tableX tableI 9 8 s := by decide
theorem row_valid_9_9 : ∀ s : Fin 10,
 (tableX 9 9 s, tableI 9 9 s) = topStep tableX tableI 9 9 s := by decide
theorem row_valid_9 : ∀ r s : Fin 10,
 (tableX 9 r s, tableI 9 r s) = topStep tableX tableI 9 r s := by
 intro r s
 fin_cases r
 · exact row_valid_9_0 s
 · exact row_valid_9_1 s
 · exact row_valid_9_2 s
 · exact row_valid_9_3 s
 · exact row_valid_9_4 s
 · exact row_valid_9_5 s
 · exact row_valid_9_6 s
 · exact row_valid_9_7 s
 · exact row_valid_9_8 s
 · exact row_valid_9_9 s
end StackSort.Seeds2
