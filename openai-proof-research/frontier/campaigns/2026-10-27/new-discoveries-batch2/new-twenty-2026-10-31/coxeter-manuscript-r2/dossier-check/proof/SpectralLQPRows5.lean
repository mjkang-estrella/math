import SpectralLPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_qp_r5 : ∀ j : Fin 18, (LQ * LP) 5 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 5 j := by decide +kernel
theorem L_qp_r6 : ∀ j : Fin 18, (LQ * LP) 6 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 6 j := by decide +kernel
theorem L_qp_r7 : ∀ j : Fin 18, (LQ * LP) 7 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 7 j := by decide +kernel
theorem L_qp_r8 : ∀ j : Fin 18, (LQ * LP) 8 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 8 j := by decide +kernel
theorem L_qp_r9 : ∀ j : Fin 18, (LQ * LP) 9 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
