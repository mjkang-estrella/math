import SpectralAData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_pq_r5 : ∀ j : Fin 19, (AP * AQ) 5 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 5 j := by decide +kernel
theorem A_pq_r6 : ∀ j : Fin 19, (AP * AQ) 6 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 6 j := by decide +kernel
theorem A_pq_r7 : ∀ j : Fin 19, (AP * AQ) 7 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 7 j := by decide +kernel
theorem A_pq_r8 : ∀ j : Fin 19, (AP * AQ) 8 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 8 j := by decide +kernel
theorem A_pq_r9 : ∀ j : Fin 19, (AP * AQ) 9 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
