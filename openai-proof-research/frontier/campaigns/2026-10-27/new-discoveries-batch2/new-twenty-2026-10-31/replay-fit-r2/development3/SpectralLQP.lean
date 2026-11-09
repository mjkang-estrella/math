import SpectralLQPRows0
import SpectralLQPRows5
import SpectralLQPRows10
import SpectralLQPRows15
import SpectralLPQ
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem L_qp : LQ * LP = 1 := by
  ext i j
  fin_cases i
  · exact L_qp_r0 j
  · exact L_qp_r1 j
  · exact L_qp_r2 j
  · exact L_qp_r3 j
  · exact L_qp_r4 j
  · exact L_qp_r5 j
  · exact L_qp_r6 j
  · exact L_qp_r7 j
  · exact L_qp_r8 j
  · exact L_qp_r9 j
  · exact L_qp_r10 j
  · exact L_qp_r11 j
  · exact L_qp_r12 j
  · exact L_qp_r13 j
  · exact L_qp_r14 j
  · exact L_qp_r15 j
  · exact L_qp_r16 j
  · exact L_qp_r17 j
end ActualSpectra330264
