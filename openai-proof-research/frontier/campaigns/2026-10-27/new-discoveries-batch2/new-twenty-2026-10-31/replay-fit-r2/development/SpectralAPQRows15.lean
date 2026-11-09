import SpectralAData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_pq_r15 : ∀ j : Fin 19, (AP * AQ) 15 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 15 j := by decide +kernel
theorem A_pq_r16 : ∀ j : Fin 19, (AP * AQ) 16 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 16 j := by decide +kernel
theorem A_pq_r17 : ∀ j : Fin 19, (AP * AQ) 17 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 17 j := by decide +kernel
theorem A_pq_r18 : ∀ j : Fin 19, (AP * AQ) 18 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 18 j := by decide +kernel
end ActualSpectra330264
