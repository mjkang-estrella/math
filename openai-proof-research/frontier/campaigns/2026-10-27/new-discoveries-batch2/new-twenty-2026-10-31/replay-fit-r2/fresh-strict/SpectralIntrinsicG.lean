import SpectralTrees
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
def edgeMapG (i : Fin 18) : G.edgeSet :=
  ⟨Sym2.mk (Fin.ofNat 19 (edgeG i).1) (Fin.ofNat 19 (edgeG i).2), by
    fin_cases i <;> decide +kernel⟩
theorem edgeMapG_bijective : Function.Bijective edgeMapG := by decide +kernel
noncomputable def edgeEquivG : Fin 18 ≃ G.edgeSet := Equiv.ofBijective edgeMapG edgeMapG_bijective
noncomputable def lineIsoG : lineG ≃g G.lineGraph where
  toEquiv := edgeEquivG
  map_rel_iff' := by
    have h : ∀ a b : Fin 18, (edgeMapG a ≠ edgeMapG b ∧ ∃ v : Fin 19, v ∈ (edgeMapG a).val ∧ v ∈ (edgeMapG b).val) ↔ lineG.Adj a b := by decide +kernel
    intro a b
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact h a b
theorem intrinsicG :
    (by classical exact (G.lineGraph.adjMatrix ℚ).charpoly) = LG.charpoly := by
  classical
  rw [← lineIsoG.reindex_adjMatrix ℚ]
  exact Matrix.charpoly_reindex _ _
#print axioms intrinsicG

end ActualSpectra330264
