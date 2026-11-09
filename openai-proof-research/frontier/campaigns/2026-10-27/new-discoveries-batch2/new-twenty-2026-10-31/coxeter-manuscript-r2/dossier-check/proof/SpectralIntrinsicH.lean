import SpectralIntrinsicG
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ActualSpectra330264
def edgeMapH (i : Fin 18) : H.edgeSet :=
  ⟨Sym2.mk (Fin.ofNat 19 (edgeH i).1) (Fin.ofNat 19 (edgeH i).2), by
    fin_cases i <;> decide +kernel⟩
theorem edgeMapH_bijective : Function.Bijective edgeMapH := by decide +kernel
noncomputable def edgeEquivH : Fin 18 ≃ H.edgeSet := Equiv.ofBijective edgeMapH edgeMapH_bijective
noncomputable def lineIsoH : lineH ≃g H.lineGraph where
  toEquiv := edgeEquivH
  map_rel_iff' := by
    have h : ∀ a b : Fin 18, (edgeMapH a ≠ edgeMapH b ∧ ∃ v : Fin 19, v ∈ (edgeMapH a).val ∧ v ∈ (edgeMapH b).val) ↔ lineH.Adj a b := by decide +kernel
    intro a b
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact h a b
theorem intrinsicH :
    (by classical exact (H.lineGraph.adjMatrix ℚ).charpoly) = LH.charpoly := by
  classical
  rw [← lineIsoH.reindex_adjMatrix ℚ]
  exact Matrix.charpoly_reindex _ _
#print axioms intrinsicH

end ActualSpectra330264
