import SpectralAData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_pq_r10 : ∀ j : Fin 19, (AP * AQ) 10 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 10 j := by decide +kernel
theorem A_pq_r11 : ∀ j : Fin 19, (AP * AQ) 11 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 11 j := by decide +kernel
theorem A_pq_r12 : ∀ j : Fin 19, (AP * AQ) 12 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 12 j := by decide +kernel
theorem A_pq_r13 : ∀ j : Fin 19, (AP * AQ) 13 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 13 j := by decide +kernel
theorem A_pq_r14 : ∀ j : Fin 19, (AP * AQ) 14 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 14 j := by decide +kernel
end ActualSpectra330264
