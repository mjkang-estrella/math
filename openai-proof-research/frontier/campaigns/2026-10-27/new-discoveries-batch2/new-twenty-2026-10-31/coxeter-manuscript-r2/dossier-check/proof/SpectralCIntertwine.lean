import SpectralCIntertwineRows0
import SpectralCIntertwineRows5
import SpectralCIntertwineRows10
import SpectralCIntertwineRows15
import SpectralCQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem C_intertwine : CG * CP = CP * CH := by
  ext i j
  fin_cases i
  · exact C_intertwine_r0 j
  · exact C_intertwine_r1 j
  · exact C_intertwine_r2 j
  · exact C_intertwine_r3 j
  · exact C_intertwine_r4 j
  · exact C_intertwine_r5 j
  · exact C_intertwine_r6 j
  · exact C_intertwine_r7 j
  · exact C_intertwine_r8 j
  · exact C_intertwine_r9 j
  · exact C_intertwine_r10 j
  · exact C_intertwine_r11 j
  · exact C_intertwine_r12 j
  · exact C_intertwine_r13 j
  · exact C_intertwine_r14 j
  · exact C_intertwine_r15 j
  · exact C_intertwine_r16 j
  · exact C_intertwine_r17 j
  · exact C_intertwine_r18 j
end ActualSpectra330264
