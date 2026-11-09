import SpectralAPQRows0
import SpectralAPQRows5
import SpectralAPQRows10
import SpectralAPQRows15
import SpectralAData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem A_pq : AP * AQ = 1 := by
  ext i j
  fin_cases i
  · exact A_pq_r0 j
  · exact A_pq_r1 j
  · exact A_pq_r2 j
  · exact A_pq_r3 j
  · exact A_pq_r4 j
  · exact A_pq_r5 j
  · exact A_pq_r6 j
  · exact A_pq_r7 j
  · exact A_pq_r8 j
  · exact A_pq_r9 j
  · exact A_pq_r10 j
  · exact A_pq_r11 j
  · exact A_pq_r12 j
  · exact A_pq_r13 j
  · exact A_pq_r14 j
  · exact A_pq_r15 j
  · exact A_pq_r16 j
  · exact A_pq_r17 j
  · exact A_pq_r18 j
end ActualSpectra330264
