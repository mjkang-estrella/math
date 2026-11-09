import SpectralAPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_qp_r0 : ∀ j : Fin 19, (AQ * AP) 0 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 0 j := by decide +kernel
theorem A_qp_r1 : ∀ j : Fin 19, (AQ * AP) 1 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 1 j := by decide +kernel
theorem A_qp_r2 : ∀ j : Fin 19, (AQ * AP) 2 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 2 j := by decide +kernel
theorem A_qp_r3 : ∀ j : Fin 19, (AQ * AP) 3 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 3 j := by decide +kernel
theorem A_qp_r4 : ∀ j : Fin 19, (AQ * AP) 4 j = (1 : Matrix (Fin 19) (Fin 19) ℚ) 4 j := by decide +kernel
end ActualSpectra330264
