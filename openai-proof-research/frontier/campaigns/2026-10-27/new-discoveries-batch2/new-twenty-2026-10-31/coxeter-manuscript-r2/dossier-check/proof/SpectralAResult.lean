import SpectralAIntertwine
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem adjacency_charpoly : AG.charpoly = AH.charpoly := charpoly_of_intertwiner _ _ AP AQ A_pq A_qp A_intertwine
#print axioms adjacency_charpoly
end ActualSpectra330264
