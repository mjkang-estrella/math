import SpectralIntrinsicH
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem intrinsic_line_charpoly :
    (by classical exact (G.lineGraph.adjMatrix ℚ).charpoly) =
    (by classical exact (H.lineGraph.adjMatrix ℚ).charpoly) := by
  rw [intrinsicG, intrinsicH]
  exact line_charpoly

theorem spectral_hypotheses : G.IsTree ∧ H.IsTree ∧
    AG.charpoly = AH.charpoly ∧ CG.charpoly = CH.charpoly :=
  ⟨treeG, treeH, adjacency_charpoly, complement_charpoly⟩
#print axioms intrinsic_line_charpoly
#print axioms spectral_hypotheses
end ActualSpectra330264
