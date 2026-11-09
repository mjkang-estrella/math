import SpectralAQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_intertwine_r5 : ∀ j : Fin 19, (AG * AP) 5 j = (AP * AH : Matrix (Fin 19) (Fin 19) ℚ) 5 j := by decide +kernel
theorem A_intertwine_r6 : ∀ j : Fin 19, (AG * AP) 6 j = (AP * AH : Matrix (Fin 19) (Fin 19) ℚ) 6 j := by decide +kernel
theorem A_intertwine_r7 : ∀ j : Fin 19, (AG * AP) 7 j = (AP * AH : Matrix (Fin 19) (Fin 19) ℚ) 7 j := by decide +kernel
theorem A_intertwine_r8 : ∀ j : Fin 19, (AG * AP) 8 j = (AP * AH : Matrix (Fin 19) (Fin 19) ℚ) 8 j := by decide +kernel
theorem A_intertwine_r9 : ∀ j : Fin 19, (AG * AP) 9 j = (AP * AH : Matrix (Fin 19) (Fin 19) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
