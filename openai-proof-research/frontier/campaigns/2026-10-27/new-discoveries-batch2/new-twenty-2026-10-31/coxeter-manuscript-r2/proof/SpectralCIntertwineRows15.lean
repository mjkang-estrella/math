import SpectralCQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_intertwine_r15 : ∀ j : Fin 19, (CG * CP) 15 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 15 j := by decide +kernel
theorem C_intertwine_r16 : ∀ j : Fin 19, (CG * CP) 16 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 16 j := by decide +kernel
theorem C_intertwine_r17 : ∀ j : Fin 19, (CG * CP) 17 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 17 j := by decide +kernel
theorem C_intertwine_r18 : ∀ j : Fin 19, (CG * CP) 18 j = (CP * CH : Matrix (Fin 19) (Fin 19) ℚ) 18 j := by decide +kernel
end ActualSpectra330264
