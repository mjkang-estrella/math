import SpectralAIntertwineRows0
import SpectralAIntertwineRows5
import SpectralAIntertwineRows10
import SpectralAIntertwineRows15
import SpectralAQP
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_intertwine : AG * AP = AP * AH := by
  ext i j
  fin_cases i
  · exact A_intertwine_r0 j
  · exact A_intertwine_r1 j
  · exact A_intertwine_r2 j
  · exact A_intertwine_r3 j
  · exact A_intertwine_r4 j
  · exact A_intertwine_r5 j
  · exact A_intertwine_r6 j
  · exact A_intertwine_r7 j
  · exact A_intertwine_r8 j
  · exact A_intertwine_r9 j
  · exact A_intertwine_r10 j
  · exact A_intertwine_r11 j
  · exact A_intertwine_r12 j
  · exact A_intertwine_r13 j
  · exact A_intertwine_r14 j
  · exact A_intertwine_r15 j
  · exact A_intertwine_r16 j
  · exact A_intertwine_r17 j
  · exact A_intertwine_r18 j
end ActualSpectra330264
