import SpectralLQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_intertwine_r15 : ∀ j : Fin 18, (LG * LP) 15 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 15 j := by decide +kernel
theorem L_intertwine_r16 : ∀ j : Fin 18, (LG * LP) 16 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 16 j := by decide +kernel
theorem L_intertwine_r17 : ∀ j : Fin 18, (LG * LP) 17 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 17 j := by decide +kernel
end ActualSpectra330264
