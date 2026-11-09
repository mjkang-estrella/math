import SpectralLIntertwineRows0
import SpectralLIntertwineRows5
import SpectralLIntertwineRows10
import SpectralLIntertwineRows15
import SpectralLQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_intertwine : LG * LP = LP * LH := by
  ext i j
  fin_cases i
  · exact L_intertwine_r0 j
  · exact L_intertwine_r1 j
  · exact L_intertwine_r2 j
  · exact L_intertwine_r3 j
  · exact L_intertwine_r4 j
  · exact L_intertwine_r5 j
  · exact L_intertwine_r6 j
  · exact L_intertwine_r7 j
  · exact L_intertwine_r8 j
  · exact L_intertwine_r9 j
  · exact L_intertwine_r10 j
  · exact L_intertwine_r11 j
  · exact L_intertwine_r12 j
  · exact L_intertwine_r13 j
  · exact L_intertwine_r14 j
  · exact L_intertwine_r15 j
  · exact L_intertwine_r16 j
  · exact L_intertwine_r17 j
end ActualSpectra330264
