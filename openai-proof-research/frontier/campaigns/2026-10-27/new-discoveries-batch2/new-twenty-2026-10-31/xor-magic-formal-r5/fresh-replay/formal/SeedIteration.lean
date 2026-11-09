import AssemblyComplement
import SeedWalkBridge
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
/-- An iteratable seed, allowing its finite enumeration to be chosen afresh. -/
def SeedExists (n d : ℕ) (closed : Bool) : Prop :=
  ∃ m : ℕ, ∃ G : SimpleGraph (Fin m), ∃ _ : DecidableRel G.Adj,
    Nonempty (ColouredSeed G n d closed)

theorem ColouredSeed.iterate [Nonempty (Fin m)] {closed : Bool}
    (S : ColouredSeed G n d closed) (hd : 4 ≤ d)
    (hpar : if closed then Even d else Odd d) : SeedExists (n+2) d closed := by
  classical
  have choose : ∃ c : OrientedEdge G → Four,
      (affineTransport G (chosenSlopes G S.colouring) c).graph.IsRegularOfDegree d ∧
      (if closed then ClosedMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2)
       else OpenMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2)) := by
    cases closed
    · obtain ⟨c,_,_,hr,hm⟩ := chosen_lift_open S hd hpar
      exact ⟨c,hr,hm⟩
    · obtain ⟨c,_,_,hr,hm⟩ := chosen_lift_closed S hd hpar
      exact ⟨c,hr,hm⟩
  obtain ⟨c,hr,hm⟩ := choose
  let T := affineTransport G (chosenSlopes G S.colouring) c
  have hn : S.walk.length % 3 ≠ 0 := by rw [S.length_eq]; exact S.seed.factorCycle.not_three
  obtain ⟨a,b,hab⟩ := nontrivial_holonomy_of_omega_walk G _ c S.walk S.oriented hn
  obtain ⟨x,hx,_⟩ := affine_unique_fixed a b
  have hf : T.along S.walk x = x := (hab x).trans hx
  let C := persistedCycle S c (S.complementInput c) x hf
  let q := T.closedLift S.walk x hf
  have hlen : q.length = C.length := (T.length_closedLift _ _ _).trans S.length_eq
  have hind : ∀ i : Fin C.length, q.getVert i.val = C.cycle i := by intro i; rfl
  have hs : C.colouring.colour (C.cycle ⟨0,C.positive⟩) = true := by
    change S.colouring.colour (q.getVert 0).1 = true
    rw [SimpleGraph.Walk.getVert_zero]
    exact S.starts_true
  let e := Fintype.equivFin (Fin m × Four)
  let H := T.graph.comap e.symm
  let f : T.graph ≃g H := (SimpleGraph.Iso.comap e.symm T.graph).symm
  refine ⟨_, H, inferInstance, ⟨?_⟩⟩
  let q' : T.graph.Walk (C.cycle ⟨0,C.positive⟩) (C.cycle ⟨0,C.positive⟩) :=
    q.copy q.getVert_zero.symm q.getVert_zero.symm
  apply seedOfRelabelledWalk C hr hm q' _ _ _ hs f
  · exact (SimpleGraph.Walk.isCycle_copy _ _).mpr (T.isCycle_closedLift _ S.isCycle x hf)
  · exact (SimpleGraph.Walk.length_copy _ _ _).trans hlen
  · intro i
    exact (SimpleGraph.Walk.getVert_copy _ _ _ _).trans (hind i)
end XorMagic
