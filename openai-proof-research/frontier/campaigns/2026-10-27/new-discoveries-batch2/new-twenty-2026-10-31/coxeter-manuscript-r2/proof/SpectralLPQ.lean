import SpectralLPQRows0
import SpectralLPQRows5
import SpectralLPQRows10
import SpectralLPQRows15
import SpectralLData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_pq : LP * LQ = 1 := by
  ext i j
  fin_cases i
  · exact L_pq_r0 j
  · exact L_pq_r1 j
  · exact L_pq_r2 j
  · exact L_pq_r3 j
  · exact L_pq_r4 j
  · exact L_pq_r5 j
  · exact L_pq_r6 j
  · exact L_pq_r7 j
  · exact L_pq_r8 j
  · exact L_pq_r9 j
  · exact L_pq_r10 j
  · exact L_pq_r11 j
  · exact L_pq_r12 j
  · exact L_pq_r13 j
  · exact L_pq_r14 j
  · exact L_pq_r15 j
  · exact L_pq_r16 j
  · exact L_pq_r17 j
end ActualSpectra330264
