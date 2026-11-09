import SpectralCPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_qp_r5 : ∀ j : Fin 19, (CQ * CP) 5 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 5 j := by decide +kernel
theorem C_qp_r6 : ∀ j : Fin 19, (CQ * CP) 6 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 6 j := by decide +kernel
theorem C_qp_r7 : ∀ j : Fin 19, (CQ * CP) 7 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 7 j := by decide +kernel
theorem C_qp_r8 : ∀ j : Fin 19, (CQ * CP) 8 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 8 j := by decide +kernel
theorem C_qp_r9 : ∀ j : Fin 19, (CQ * CP) 9 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
