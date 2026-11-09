import SpectralCQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_intertwine_r0 : ∀ j : Fin 19, (CG * CP) 0 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 0 j := by decide +kernel
theorem C_intertwine_r1 : ∀ j : Fin 19, (CG * CP) 1 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 1 j := by decide +kernel
theorem C_intertwine_r2 : ∀ j : Fin 19, (CG * CP) 2 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 2 j := by decide +kernel
theorem C_intertwine_r3 : ∀ j : Fin 19, (CG * CP) 3 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 3 j := by decide +kernel
theorem C_intertwine_r4 : ∀ j : Fin 19, (CG * CP) 4 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 4 j := by decide +kernel
end ActualSpectra330264
