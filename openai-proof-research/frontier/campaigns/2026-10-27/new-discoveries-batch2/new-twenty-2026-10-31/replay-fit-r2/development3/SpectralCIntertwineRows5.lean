import SpectralCQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_intertwine_r5 : ∀ j : Fin 19, (CG * CP) 5 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 5 j := by decide +kernel
theorem C_intertwine_r6 : ∀ j : Fin 19, (CG * CP) 6 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 6 j := by decide +kernel
theorem C_intertwine_r7 : ∀ j : Fin 19, (CG * CP) 7 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 7 j := by decide +kernel
theorem C_intertwine_r8 : ∀ j : Fin 19, (CG * CP) 8 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 8 j := by decide +kernel
theorem C_intertwine_r9 : ∀ j : Fin 19, (CG * CP) 9 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 9 j := by decide +kernel
end ActualSpectra330264
