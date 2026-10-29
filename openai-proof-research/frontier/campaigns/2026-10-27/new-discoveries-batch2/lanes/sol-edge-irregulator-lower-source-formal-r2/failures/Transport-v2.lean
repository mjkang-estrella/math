import Lower
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
def moveSet (e : V ≃ W) (S : Finset (Sym2 V)) : Finset (Sym2 W) :=
  S.map e.toEmbedding.sym2Map
 theorem moveSet_card (e : V ≃ W) (S : Finset (Sym2 V)) : (moveSet e S).card = S.card :=
  Finset.card_map _
 theorem moveSet_mem (e : V ≃ W) (S : Finset (Sym2 V)) (u v : V) :
    s(e u,e v) ∈ moveSet e S ↔ s(u,v) ∈ S := by
  change e.toEmbedding.sym2Map s(u,v) ∈ S.map e.toEmbedding.sym2Map ↔ _
  exact Finset.mem_map' _
 def retainedIso (f : G ≃g H) (S : Finset (Sym2 V)) :
    Retained G S ≃g Retained H (moveSet f.toEquiv S) where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro u v
    simp only [Retained,deleteEdges_adj,Finset.mem_coe,moveSet_mem,f.map_rel_iff]
 theorem valid_move (f : G ≃g H) (S : Finset (Sym2 V)) (h : Valid G S) :
    Valid H (moveSet f.toEquiv S) := by
  constructor
  · intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
    induction a using Sym2.inductionOn with
    | _ u v =>
      have hh := h.1 ha
      rw [mem_edgeFinset] at hh ⊢
      exact f.map_rel_iff.mpr hh
  · intro u v huv
    obtain ⟨a,rfl⟩ := f.toEquiv.surjective u
    obtain ⟨b,rfl⟩ := f.toEquiv.surjective v
    have fi := retainedIso f S
    have hh := h.2 a b (fi.map_rel_iff.mp huv)
    simpa only [← fi.degree_eq] using hh
 theorem minimum_iso (f : G ≃g H) : minimum G = minimum H := by
  apply Nat.le_antisymm
  · obtain ⟨S,hs,hc⟩ := minimum_attained H
    have := minimum_le G _ (valid_move f.symm S hs)
    simpa only [moveSet_card,hc] using this
  · obtain ⟨S,hs,hc⟩ := minimum_attained G
    have := minimum_le H _ (valid_move f S hs)
    simpa only [moveSet_card,hc] using this
 def finGraph (t : ℕ) : SimpleGraph (Fin (Fintype.card (Vertex t))) :=
    (graph t).map (Fintype.equivFin (Vertex t))
 def finIso (t : ℕ) : graph t ≃g finGraph t := Iso.map (Fintype.equivFin (Vertex t)) _
 theorem fin_connected (t : ℕ) : (finGraph t).Connected :=
    (graph_connected t).map (finIso t).toHom (finIso t).toEquiv.surjective
 theorem fin_edge_card (t : ℕ) : (finGraph t).edgeFinset.card = 8*t :=
    ((finIso t).card_edgeFinset_eq.symm).trans (edge_card t)
 theorem fin_minimum_lower (t : ℕ) : 3*t ≤ minimum (finGraph t) := by
    rw [← minimum_iso (finIso t)]
    exact minimum_lower t
end
end EdgeIrregulator
