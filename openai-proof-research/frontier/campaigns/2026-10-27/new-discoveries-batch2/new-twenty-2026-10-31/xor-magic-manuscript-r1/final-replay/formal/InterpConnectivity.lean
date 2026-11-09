import InterpGraph
set_option linter.unusedSectionVars false
namespace XorMagic

theorem four_avoid_two : ∀ x z : Four, ∃ y : Four, y ≠ x ∧ y ≠ z := by decide

variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {d c : ℕ}
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d) (H : MatchingDecomposition Gᶜ c)

theorem interp_block_edge (k j : ℕ) (hj : j ≤ c) (i : Fin d)
    (a : InterpAllowed k i) (p : V × Four) :
    (T.interpGraph F H k j hj).Adj p (blockMate F (T.matchingChart F) i a.1 p) :=
  ⟨.inl ⟨i,a⟩,rfl⟩

theorem interp_selected_fibre (k j : ℕ) (hj : j ≤ c) (i : Fin d) (hi : i.val < k)
    (v : V) (x z : Four) :
    (T.interpGraph F H k j hj).Reachable (v,x) (v,z) := by
  obtain ⟨y,hyx,hyz⟩ := four_avoid_two (T.matchingChart F i v x) (T.matchingChart F i v z)
  let a : InterpAllowed k i := ⟨y-T.matchingChart F i v x,by simp only [hi,ite_true]; exact sub_ne_zero.mpr hyx⟩
  let b : InterpAllowed k i := ⟨y-T.matchingChart F i v z,by simp only [hi,ite_true]; exact sub_ne_zero.mpr hyz⟩
  have ha := T.interp_block_edge F H k j hj i a (v,x)
  have hb := T.interp_block_edge F H k j hj i b (v,z)
  have he : blockMate F (T.matchingChart F) i a.1 (v,x) =
      blockMate F (T.matchingChart F) i b.1 (v,z) := by
    simp [blockMate,a,b]
  exact ha.reachable.trans (he ▸ hb.reachable.symm)

theorem interp_edge_surjective (k j : ℕ) (hj : j ≤ c) {u v : V} (huv : G.Adj u v)
    (y : Four) : ∃ x : Four, (T.interpGraph F H k j hj).Adj (u,x) (v,y) := by
  obtain ⟨i,hi⟩ := (F.cover _ _).mp huv.symm
  let a : InterpAllowed k i := ⟨if i.val < k then (1,0) else 0, by
    split_ifs <;> simp_all⟩
  have he := T.interp_block_edge F H k j hj i a (v,y)
  refine ⟨(blockMate F (T.matchingChart F) i a.1 (v,y)).2, ?_⟩
  have hh : blockMate F (T.matchingChart F) i a.1 (v,y) =
    (u,(blockMate F (T.matchingChart F) i a.1 (v,y)).2) := Prod.ext hi rfl
  exact hh ▸ he.symm

theorem interp_full_transfer (k j : ℕ) (hj : j ≤ c) (r : V × Four)
    {u v : V} (h : G.Reachable u v)
    (full : ∀ x, (T.interpGraph F H k j hj).Reachable r (u,x)) :
    ∀ y, (T.interpGraph F H k j hj).Reachable r (v,y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact full
  | cons he _ ih =>
    apply ih
    intro y
    obtain ⟨x,hx⟩ := T.interp_edge_surjective F H k j hj he y
    exact (full x).trans hx.reachable

theorem interpGraph_connected (k j : ℕ) (hj : j ≤ c) (hG : G.Connected)
    (hT : T.graph.Connected) : (T.interpGraph F H k j hj).Connected := by
  let : Nonempty V := hG.nonempty
  by_cases hk : k = 0
  · subst k
    apply hT.mono
    intro p q hpq
    obtain ⟨i,hi⟩ := (F.cover _ _).mp hpq.1
    refine ⟨.inl ⟨i,⟨0,by simp⟩⟩,?_⟩
    change blockMate F (T.matchingChart F) i 0 p = q
    rw [T.blockMate_zero F]
    exact Prod.ext hi (by simpa only [hi] using hpq.2)
  · by_cases hd : d = 0
    · have : IsEmpty (Fin d) := by rw [hd]; infer_instance
      have he : G = ⊥ := by
        ext u v
        simp [F.cover]
      have hh : T.graph = ⊥ := by ext p q; simp [EdgeTransport.graph,he]
      have hbad := hT.preconnected (Classical.choice inferInstance, (0 : Four))
        (Classical.choice inferInstance, (1 : Four))
      rw [hh, SimpleGraph.reachable_bot] at hbad
      have := congrArg Prod.snd hbad
      norm_num at this
    · let i : Fin d := ⟨0,by omega⟩
      let v : V := Classical.choice inferInstance
      have full : ∀ w y, (T.interpGraph F H k j hj).Reachable (v,0) (w,y) := by
        intro w
        apply T.interp_full_transfer F H k j hj (v,0) (hG.preconnected v w)
        intro x
        exact T.interp_selected_fibre F H k j hj i (by dsimp [i]; omega) v 0 x
      exact ⟨fun p q => (full p.1 p.2).symm.trans (full q.1 q.2)⟩
end EdgeTransport
end XorMagic
