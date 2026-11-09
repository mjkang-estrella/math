import SpectralCIntertwine
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
theorem complement_charpoly : CG.charpoly = CH.charpoly := charpoly_of_intertwiner _ _ CP CQ C_pq C_qp C_intertwine
#print axioms complement_charpoly
end ActualSpectra330264
