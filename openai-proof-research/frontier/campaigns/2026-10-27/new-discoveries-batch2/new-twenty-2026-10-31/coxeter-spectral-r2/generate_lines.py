from pathlib import Path
w=Path(__file__).resolve().parent;s='import Mathlib.Combinatorics.SimpleGraph.LineGraph\nimport Mathlib.Tactic.FinCases\n'+(w/'SpectralDefinitions.lean').read_text().replace('end ActualSpectra330264','')
for k in ['G','H']:
 s+=f'''
def edgeMap{k} (i : Fin 18) : {k}.edgeSet :=
  ⟨Sym2.mk (Fin.ofNat 19 (edge{k} i).1) (Fin.ofNat 19 (edge{k} i).2), by
    fin_cases i <;> decide +kernel⟩
theorem edgeMap{k}_bijective : Function.Bijective edgeMap{k} := by decide +kernel
noncomputable def edgeEquiv{k} : Fin 18 ≃ {k}.edgeSet := Equiv.ofBijective edgeMap{k} edgeMap{k}_bijective
noncomputable def lineIso{k} : line{k} ≃g {k}.lineGraph where
  toEquiv := edgeEquiv{k}
  map_rel_iff' := by
    have h : ∀ a b : Fin 18, (edgeMap{k} a ≠ edgeMap{k} b ∧ ∃ v : Fin 19, v ∈ (edgeMap{k} a).val ∧ v ∈ (edgeMap{k} b).val) ↔ line{k}.Adj a b := by decide +kernel
    intro a b
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact h a b
theorem intrinsic{k} :
    (by classical exact ({k}.lineGraph.adjMatrix ℚ).charpoly) = L{k}.charpoly := by
  classical
  rw [← lineIso{k}.reindex_adjMatrix ℚ]
  exact Matrix.charpoly_reindex _ _
#print axioms intrinsic{k}
'''
s+='end ActualSpectra330264\n';(w/'CanonicalLines.lean').write_text(s)
