import SpectralCData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_pq_r0 : ∀ j : Fin 19, (CP * CQ) 0 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 0 j := by decide +kernel
theorem C_pq_r1 : ∀ j : Fin 19, (CP * CQ) 1 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 1 j := by decide +kernel
theorem C_pq_r2 : ∀ j : Fin 19, (CP * CQ) 2 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 2 j := by decide +kernel
theorem C_pq_r3 : ∀ j : Fin 19, (CP * CQ) 3 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 3 j := by decide +kernel
theorem C_pq_r4 : ∀ j : Fin 19, (CP * CQ) 4 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 4 j := by decide +kernel
end ActualSpectra330264
