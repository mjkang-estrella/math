import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_6_0 : ∀ s : Fin 7,
 (tableX 6 0 s, tableI 6 0 s) = topStep tableX tableI 6 0 s := by decide
theorem row_valid_6_1 : ∀ s : Fin 7,
 (tableX 6 1 s, tableI 6 1 s) = topStep tableX tableI 6 1 s := by decide
theorem row_valid_6_2 : ∀ s : Fin 7,
 (tableX 6 2 s, tableI 6 2 s) = topStep tableX tableI 6 2 s := by decide
theorem row_valid_6_3 : ∀ s : Fin 7,
 (tableX 6 3 s, tableI 6 3 s) = topStep tableX tableI 6 3 s := by decide
theorem row_valid_6_4 : ∀ s : Fin 7,
 (tableX 6 4 s, tableI 6 4 s) = topStep tableX tableI 6 4 s := by decide
theorem row_valid_6_5 : ∀ s : Fin 7,
 (tableX 6 5 s, tableI 6 5 s) = topStep tableX tableI 6 5 s := by decide
theorem row_valid_6_6 : ∀ s : Fin 7,
 (tableX 6 6 s, tableI 6 6 s) = topStep tableX tableI 6 6 s := by decide
theorem row_valid_6 : ∀ r s : Fin 7,
 (tableX 6 r s, tableI 6 r s) = topStep tableX tableI 6 r s := by
 intro r s
 fin_cases r
 · exact row_valid_6_0 s
 · exact row_valid_6_1 s
 · exact row_valid_6_2 s
 · exact row_valid_6_3 s
 · exact row_valid_6_4 s
 · exact row_valid_6_5 s
 · exact row_valid_6_6 s
end StackSort.Seeds2
