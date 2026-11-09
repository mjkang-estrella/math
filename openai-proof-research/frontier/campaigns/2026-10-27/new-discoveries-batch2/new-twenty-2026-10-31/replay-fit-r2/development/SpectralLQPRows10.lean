import SpectralLPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_qp_r10 : ∀ j : Fin 18, (LQ * LP) 10 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 10 j := by decide +kernel
theorem L_qp_r11 : ∀ j : Fin 18, (LQ * LP) 11 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 11 j := by decide +kernel
theorem L_qp_r12 : ∀ j : Fin 18, (LQ * LP) 12 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 12 j := by decide +kernel
theorem L_qp_r13 : ∀ j : Fin 18, (LQ * LP) 13 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 13 j := by decide +kernel
theorem L_qp_r14 : ∀ j : Fin 18, (LQ * LP) 14 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 14 j := by decide +kernel
end ActualSpectra330264
