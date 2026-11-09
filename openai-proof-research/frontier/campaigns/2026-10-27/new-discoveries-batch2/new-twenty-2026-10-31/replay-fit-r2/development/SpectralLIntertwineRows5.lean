import SpectralLQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_intertwine_r5 : ∀ j : Fin 18, (LG * LP) 5 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 5 j := by decide +kernel
theorem L_intertwine_r6 : ∀ j : Fin 18, (LG * LP) 6 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 6 j := by decide +kernel
theorem L_intertwine_r7 : ∀ j : Fin 18, (LG * LP) 7 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 7 j := by decide +kernel
theorem L_intertwine_r8 : ∀ j : Fin 18, (LG * LP) 8 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 8 j := by decide +kernel
theorem L_intertwine_r9 : ∀ j : Fin 18, (LG * LP) 9 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
