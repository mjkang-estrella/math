import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_10_0 : ∀ s : Fin 11,
 (tableX 10 0 s, tableI 10 0 s) = topStep tableX tableI 10 0 s := by decide
theorem row_valid_10_1 : ∀ s : Fin 11,
 (tableX 10 1 s, tableI 10 1 s) = topStep tableX tableI 10 1 s := by decide
theorem row_valid_10_2 : ∀ s : Fin 11,
 (tableX 10 2 s, tableI 10 2 s) = topStep tableX tableI 10 2 s := by decide
theorem row_valid_10_3 : ∀ s : Fin 11,
 (tableX 10 3 s, tableI 10 3 s) = topStep tableX tableI 10 3 s := by decide
theorem row_valid_10_4 : ∀ s : Fin 11,
 (tableX 10 4 s, tableI 10 4 s) = topStep tableX tableI 10 4 s := by decide
theorem row_valid_10_5 : ∀ s : Fin 11,
 (tableX 10 5 s, tableI 10 5 s) = topStep tableX tableI 10 5 s := by decide
theorem row_valid_10_6 : ∀ s : Fin 11,
 (tableX 10 6 s, tableI 10 6 s) = topStep tableX tableI 10 6 s := by decide
theorem row_valid_10_7 : ∀ s : Fin 11,
 (tableX 10 7 s, tableI 10 7 s) = topStep tableX tableI 10 7 s := by decide
theorem row_valid_10_8 : ∀ s : Fin 11,
 (tableX 10 8 s, tableI 10 8 s) = topStep tableX tableI 10 8 s := by decide
theorem row_valid_10_9 : ∀ s : Fin 11,
 (tableX 10 9 s, tableI 10 9 s) = topStep tableX tableI 10 9 s := by decide
theorem row_valid_10_10 : ∀ s : Fin 11,
 (tableX 10 10 s, tableI 10 10 s) = topStep tableX tableI 10 10 s := by decide
theorem row_valid_10 : ∀ r s : Fin 11,
 (tableX 10 r s, tableI 10 r s) = topStep tableX tableI 10 r s := by
 intro r s
 fin_cases r
 · exact row_valid_10_0 s
 · exact row_valid_10_1 s
 · exact row_valid_10_2 s
 · exact row_valid_10_3 s
 · exact row_valid_10_4 s
 · exact row_valid_10_5 s
 · exact row_valid_10_6 s
 · exact row_valid_10_7 s
 · exact row_valid_10_8 s
 · exact row_valid_10_9 s
 · exact row_valid_10_10 s
end StackSort.Seeds2
