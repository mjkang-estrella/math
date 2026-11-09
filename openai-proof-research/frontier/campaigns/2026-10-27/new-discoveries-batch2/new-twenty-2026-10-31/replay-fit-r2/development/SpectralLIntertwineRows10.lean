import SpectralLQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_intertwine_r10 : ∀ j : Fin 18, (LG * LP) 10 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 10 j := by decide +kernel
theorem L_intertwine_r11 : ∀ j : Fin 18, (LG * LP) 11 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 11 j := by decide +kernel
theorem L_intertwine_r12 : ∀ j : Fin 18, (LG * LP) 12 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 12 j := by decide +kernel
theorem L_intertwine_r13 : ∀ j : Fin 18, (LG * LP) 13 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 13 j := by decide +kernel
theorem L_intertwine_r14 : ∀ j : Fin 18, (LG * LP) 14 j = (LP * LH : Matrix (Fin 18) (Fin 18) ℚ) 14 j := by decide +kernel
end ActualSpectra330264
