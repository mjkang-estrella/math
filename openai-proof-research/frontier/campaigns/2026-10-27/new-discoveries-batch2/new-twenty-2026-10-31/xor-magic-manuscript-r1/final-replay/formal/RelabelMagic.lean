import RelabelFactors
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {n d : ℕ}
theorem relabel_neighbor_sum (e : G ≃g H) (l : V → Bits n) (v : W) :
    (∑ w ∈ H.neighborFinset v, l (e.symm w)) = ∑ u ∈ G.neighborFinset (e.symm v), l u := by
  classical
  apply Finset.sum_bij (fun w _ => e.symm w)
  · intro w hw
    simpa only [SimpleGraph.mem_neighborFinset, ← e.symm.map_adj_iff] using hw
  · intro a _ b _ h
    exact e.symm.injective h
  · intro u hu
    refine ⟨e u, ?_, by simp⟩
    simpa only [SimpleGraph.mem_neighborFinset, ← e.map_adj_iff, RelIso.apply_symm_apply] using hu
  · intro w _; rfl

theorem relabel_regular (e : G ≃g H) (h : G.IsRegularOfDegree d) : H.IsRegularOfDegree d := by
  intro w
  have hc := Fintype.card_congr (e.mapNeighborSet (e.symm w))
  have hh : H.degree w = G.degree (e.symm w) := by
    simpa only [RelIso.apply_symm_apply, SimpleGraph.card_neighborSet_eq_degree] using hc.symm
  exact hh.trans (h _)

theorem relabel_open (e : G ≃g H) (h : OpenMagic G n) : OpenMagic H n := by
  obtain ⟨hc,l,hl⟩ := h
  refine ⟨?_, e.symm.toEquiv.trans l, ?_⟩
  · exact hc.map e.toHom e.surjective
  · intro w
    exact (relabel_neighbor_sum e l w).trans (hl _)

theorem relabel_closed (e : G ≃g H) (h : ClosedMagic G n) : ClosedMagic H n := by
  obtain ⟨hc,l,hl⟩ := h
  refine ⟨?_, e.symm.toEquiv.trans l, ?_⟩
  · exact hc.map e.toHom e.surjective
  · intro w
    change l (e.symm w) + (∑ u ∈ H.neighborFinset w, l (e.symm u)) = 0
    rw [relabel_neighbor_sum]
    exact hl _
end XorMagic
