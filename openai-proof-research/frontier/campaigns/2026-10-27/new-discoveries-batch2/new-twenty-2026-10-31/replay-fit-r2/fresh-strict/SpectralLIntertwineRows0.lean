import SpectralLQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_intertwine_r0 : ∀ j : Fin 18, (LG * LP) 0 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 0 j := by decide +kernel
theorem L_intertwine_r1 : ∀ j : Fin 18, (LG * LP) 1 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 1 j := by decide +kernel
theorem L_intertwine_r2 : ∀ j : Fin 18, (LG * LP) 2 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 2 j := by decide +kernel
theorem L_intertwine_r3 : ∀ j : Fin 18, (LG * LP) 3 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 3 j := by decide +kernel
theorem L_intertwine_r4 : ∀ j : Fin 18, (LG * LP) 4 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 4 j := by decide +kernel
end ActualSpectra330264
