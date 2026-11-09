import SpectralLPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_qp_r0 : ∀ j : Fin 18, (LQ * LP) 0 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 0 j := by decide +kernel
theorem L_qp_r1 : ∀ j : Fin 18, (LQ * LP) 1 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 1 j := by decide +kernel
theorem L_qp_r2 : ∀ j : Fin 18, (LQ * LP) 2 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 2 j := by decide +kernel
theorem L_qp_r3 : ∀ j : Fin 18, (LQ * LP) 3 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 3 j := by decide +kernel
theorem L_qp_r4 : ∀ j : Fin 18, (LQ * LP) 4 j = (1 : Matrix (Fin 18) (Fin 18) ℚ) 4 j := by decide +kernel
end ActualSpectra330264
