import StackSortSeeds2Data
import Mathlib.Tactic.FinCases
namespace StackSort.Seeds2
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem row_valid_16_0 : ∀ s : Fin 6,
 (tableX 16 0 s, tableI 16 0 s) = topStep tableX tableI 16 0 s := by decide
theorem row_valid_16_1 : ∀ s : Fin 6,
 (tableX 16 1 s, tableI 16 1 s) = topStep tableX tableI 16 1 s := by decide
theorem row_valid_16_2 : ∀ s : Fin 6,
 (tableX 16 2 s, tableI 16 2 s) = topStep tableX tableI 16 2 s := by decide
theorem row_valid_16_3 : ∀ s : Fin 6,
 (tableX 16 3 s, tableI 16 3 s) = topStep tableX tableI 16 3 s := by decide
theorem row_valid_16_4 : ∀ s : Fin 6,
 (tableX 16 4 s, tableI 16 4 s) = topStep tableX tableI 16 4 s := by decide
theorem row_valid_16_5 : ∀ s : Fin 6,
 (tableX 16 5 s, tableI 16 5 s) = topStep tableX tableI 16 5 s := by decide
theorem row_valid_16 : ∀ r s : Fin 6,
 (tableX 16 r s, tableI 16 r s) = topStep tableX tableI 16 r s := by
 intro r s
 fin_cases r
 · exact row_valid_16_0 s
 · exact row_valid_16_1 s
 · exact row_valid_16_2 s
 · exact row_valid_16_3 s
 · exact row_valid_16_4 s
 · exact row_valid_16_5 s
end StackSort.Seeds2
