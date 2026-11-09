import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_12_0 : ∀ s : Fin 10,
 (tableX 12 0 s, tableI 12 0 s) = topStep tableX tableI 12 0 s := by decide
theorem row_valid_12_1 : ∀ s : Fin 10,
 (tableX 12 1 s, tableI 12 1 s) = topStep tableX tableI 12 1 s := by decide
theorem row_valid_12_2 : ∀ s : Fin 10,
 (tableX 12 2 s, tableI 12 2 s) = topStep tableX tableI 12 2 s := by decide
theorem row_valid_12_3 : ∀ s : Fin 10,
 (tableX 12 3 s, tableI 12 3 s) = topStep tableX tableI 12 3 s := by decide
theorem row_valid_12_4 : ∀ s : Fin 10,
 (tableX 12 4 s, tableI 12 4 s) = topStep tableX tableI 12 4 s := by decide
theorem row_valid_12_5 : ∀ s : Fin 10,
 (tableX 12 5 s, tableI 12 5 s) = topStep tableX tableI 12 5 s := by decide
theorem row_valid_12_6 : ∀ s : Fin 10,
 (tableX 12 6 s, tableI 12 6 s) = topStep tableX tableI 12 6 s := by decide
theorem row_valid_12_7 : ∀ s : Fin 10,
 (tableX 12 7 s, tableI 12 7 s) = topStep tableX tableI 12 7 s := by decide
theorem row_valid_12_8 : ∀ s : Fin 10,
 (tableX 12 8 s, tableI 12 8 s) = topStep tableX tableI 12 8 s := by decide
theorem row_valid_12_9 : ∀ s : Fin 10,
 (tableX 12 9 s, tableI 12 9 s) = topStep tableX tableI 12 9 s := by decide
theorem row_valid_12 : ∀ r s : Fin 10,
 (tableX 12 r s, tableI 12 r s) = topStep tableX tableI 12 r s := by
 intro r s
 fin_cases r
 · exact row_valid_12_0 s
 · exact row_valid_12_1 s
 · exact row_valid_12_2 s
 · exact row_valid_12_3 s
 · exact row_valid_12_4 s
 · exact row_valid_12_5 s
 · exact row_valid_12_6 s
 · exact row_valid_12_7 s
 · exact row_valid_12_8 s
 · exact row_valid_12_9 s
end StackSort.Seeds2
