import LiftGraph
namespace XorMagic.EdgeTransport
variable {V : Type} {G : SimpleGraph V}
variable (T : EdgeTransport G)

/-- The part of a lifted connected component in a specified base fibre. -/
noncomputable def fibre (r : V × Four) (v : V) : Finset Four :=
  @Finset.filter Four (fun x => T.graph.Reachable r (v,x)) (Classical.decPred _) Finset.univ

theorem mem_fibre (r : V × Four) (v : V) (x : Four) :
    x ∈ T.fibre r v ↔ T.graph.Reachable r (v,x) := by
  classical
  simp [fibre]

theorem fibre_transport (r : V × Four) {u v : V} (h : G.Adj u v) (x : Four) :
    x ∈ T.fibre r u ↔ T.map u v x ∈ T.fibre r v := by
  rw [T.mem_fibre, T.mem_fibre]
  have edge : T.graph.Adj (u,x) (v,T.map u v x) := ⟨h,rfl⟩
  exact ⟨fun hr => hr.trans edge.reachable, fun hr => hr.trans edge.symm.reachable⟩

noncomputable def fibreEquiv (r : V × Four) {u v : V} (h : G.Adj u v) :
    {x // x ∈ T.fibre r u} ≃ {x // x ∈ T.fibre r v} where
  toFun x := ⟨T.map u v x, (T.fibre_transport r h x).mp x.property⟩
  invFun y := ⟨T.map v u y, (T.fibre_transport r h.symm y).mp y.property⟩
  left_inv x := Subtype.ext (T.reverse h x)
  right_inv y := Subtype.ext (T.reverse h.symm y)

theorem fibre_card_adj (r : V × Four) {u v : V} (h : G.Adj u v) :
    (T.fibre r u).card = (T.fibre r v).card := by
  simpa using Fintype.card_congr (T.fibreEquiv r h)

theorem fibre_card_reachable (r : V × Four) {u v : V} (h : G.Reachable u v) :
    (T.fibre r u).card = (T.fibre r v).card := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (T.fibre_card_adj r h).trans ih

theorem fibre_nonempty_of_connected (hG : G.Connected) (r : V × Four) (v : V) :
    0 < (T.fibre r v).card := by
  have h : r.2 ∈ T.fibre r r.1 := (T.mem_fibre _ _ _).mpr .rfl
  rw [← T.fibre_card_reachable r (hG.preconnected r.1 v)]
  exact Finset.card_pos.mpr ⟨r.2,h⟩

/-- Connectivity reduces to fullness of component fibres. No holonomy claim is assumed here. -/
theorem connected_of_full_fibres [Nonempty V]
    (full : ∀ r : V × Four, ∀ v, (T.fibre r v).card = 4) : T.graph.Connected := by
  refine ⟨?_⟩
  intro p q
  apply (T.mem_fibre p q.1 q.2).mp
  have h : T.fibre p q.1 = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using full p q.1
  rw [h]
  exact Finset.mem_univ _
end XorMagic.EdgeTransport
