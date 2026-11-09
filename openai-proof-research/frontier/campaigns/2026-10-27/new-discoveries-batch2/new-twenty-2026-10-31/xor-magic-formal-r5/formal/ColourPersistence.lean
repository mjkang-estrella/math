import ColourWalks
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
noncomputable def persistedCycle {closed : Bool} (S : ColouredSeed G n d closed)
    (c : OrientedEdge G → Four) (C : LiftComplementInput G (chosenSlopes G S.colouring) c d)
    (x : Four) (hx : (affineTransport G (chosenSlopes G S.colouring) c).along S.walk x = x) :
    ColouredCycleData (affineTransport G (chosenSlopes G S.colouring) c).graph d := by
  let T := affineTransport G (chosenSlopes G S.colouring) c
  let q := T.closedLift S.walk x hx
  have hlen : q.length = S.seed.factorCycle.length := (T.length_closedLift _ _ _).trans S.length_eq
  have hcy : q.IsCycle := T.isCycle_closedLift _ S.isCycle _ _
  have hproj (i : ℕ) : (q.getVert i).1 = S.walk.getVert i := by
    have hp := T.map_closedLift S.walk x hx
    have hv := congrArg (fun p => p.getVert i) hp
    rw [SimpleGraph.Walk.getVert_map] at hv
    exact hv
  let L := S.seed.factorCycle.length
  have hpos : 0 < L := S.seed.factorCycle.positive
  let cyc : Fin L → Fin m × Four := fun i => q.getVert i.val
  have hnext (i : Fin L) : cyc ⟨(i.val+1)%L, Nat.mod_lt _ hpos⟩ = q.getVert (i.val+1) := by
    dsimp [cyc]
    by_cases h : i.val+1 < L
    · rw [Nat.mod_eq_of_lt h]
    · have he : i.val+1 = L := by have := i.isLt; omega
      rw [he,Nat.mod_self]
      rw [show L = q.length from hlen.symm]
      rw [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length]
  have hadj (i : Fin L) : T.graph.Adj (cyc i) (cyc ⟨(i.val+1)%L, Nat.mod_lt _ hpos⟩) := by
    rw [hnext]; exact q.adj_getVert_succ (by rw [hlen]; exact i.isLt)
  have hfirst (i : Fin L) : (cyc i).1 = S.seed.factorCycle.cycle i :=
    (hproj i.val).trans (S.indexed i)
  have hedge (i : Fin L) :
      (T.matching S.seed.factorCycle.factors).mate ⟨0,by have := S.seed.factorCycle.two_le; omega⟩ (cyc i) = cyc ⟨(i.val+1)%L,Nat.mod_lt _ hpos⟩ ∨
      (T.matching S.seed.factorCycle.factors).mate ⟨1,by have := S.seed.factorCycle.two_le; omega⟩ (cyc i) = cyc ⟨(i.val+1)%L,Nat.mod_lt _ hpos⟩ := by
    have hs := S.seed.factorCycle.edges i
    have liftEdge (j : Fin d) (hj : S.seed.factorCycle.factors.mate j (S.seed.factorCycle.cycle i) =
        S.seed.factorCycle.cycle ⟨(i.val+1)%L,Nat.mod_lt _ hpos⟩) :
        (T.matching S.seed.factorCycle.factors).mate j (cyc i) = cyc ⟨(i.val+1)%L,Nat.mod_lt _ hpos⟩ := by
      have hv : S.seed.factorCycle.factors.mate j (cyc i).1 = (cyc ⟨(i.val+1)%L,Nat.mod_lt _ hpos⟩).1 := by
        rw [hfirst,hfirst]; exact hj
      apply Prod.ext hv
      change T.map (cyc i).1 (S.seed.factorCycle.factors.mate j (cyc i).1) (cyc i).2 = _
      rw [hv]; exact (hadj i).2
    exact hs.elim (fun h => Or.inl (liftEdge _ h)) (fun h => Or.inr (liftEdge _ h))
  refine { factors := T.matching S.seed.factorCycle.factors
           complementFactors := ?_
           two_le := S.seed.factorCycle.two_le
           length := L
           positive := hpos
           not_three := S.seed.factorCycle.not_three
           cycle := cyc
           injective := ?_
           edges := hedge
           three_le := S.strong
           colouring := S.colouring.lift T
           outgoing := ?_ }
  · convert C.factors using 1; simp [Fintype.card_prod, Fintype.card_fin, Four, Nat.mul_comm]
  · intro i j hij
    apply Fin.ext
    exact hcy.getVert_injOn' (by rw [hlen]; exact Nat.le_sub_one_of_lt i.isLt)
      (by rw [hlen]; exact Nat.le_sub_one_of_lt j.isLt) hij
  · intro i
    rw [FactorColouring.directed_lift _ T (hadj i), hfirst, hfirst]
    exact S.colouredCycle.outgoing i
end XorMagic
