module
public import URMatchingSurvivorGraph
public import URMatchingBase
public import Mathlib.Combinatorics.SimpleGraph.Maps
@[expose] public section
namespace URMatching
universe u
variable {V : Type u}

theorem inducedGraph_eq_induce (G : SimpleGraph V) (P : Set V) :
    inducedGraph G P = G.induce P := by
  ext u v
  rfl

end URMatching
