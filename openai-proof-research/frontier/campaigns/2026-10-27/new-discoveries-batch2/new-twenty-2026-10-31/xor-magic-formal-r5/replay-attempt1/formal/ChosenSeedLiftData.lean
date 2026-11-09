import ChosenLiftMagic
import ColourPersistence
namespace XorMagic
/-- Generic seed data before relabelling the product vertex type to Bits. -/
structure ColouredLiftSeed {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n d : ℕ) (closed : Bool) where
  regular : G.IsRegularOfDegree d
  magic : if closed then ClosedMagic G n else OpenMagic G n
  cycle : ColouredCycleData G d

variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
/-- Product-type seed assembly. Complement factors are a genuine external hypothesis.
This is not the requested iteratable Bits-to-Bits seed-lift endpoint. -/
theorem chosen_seed_lift_data [Nonempty (Fin m)] {closed : Bool}
    (S : ColouredSeed G n d closed) (hd : 4 ≤ d)
    (hparity : if closed then Even d else Odd d)
    (hcomp : ∀ c : OrientedEdge G → Four,
      LiftComplementInput G (chosenSlopes G S.colouring) c d) :
    ∃ c : OrientedEdge G → Four,
      Nonempty (ColouredLiftSeed (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2) d closed) := by
  have choose : ∃ c : OrientedEdge G → Four,
      incidenceB G (chosenSlopes G S.colouring) c = 0 ∧
      c ∉ (incidenceD G (chosenSlopes G S.colouring)).range ∧
      (affineTransport G (chosenSlopes G S.colouring) c).graph.IsRegularOfDegree d ∧
      (if closed then ClosedMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2)
       else OpenMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2)) := by
    cases closed
    · exact chosen_lift_open S hd hparity
    · exact chosen_lift_closed S hd hparity
  obtain ⟨c,_,_,hreg,hmag⟩ := choose
  have hn : S.walk.length % 3 ≠ 0 := by rw [S.length_eq]; exact S.seed.factorCycle.not_three
  obtain ⟨a,b,hab⟩ := nontrivial_holonomy_of_omega_walk G _ c S.walk S.oriented hn
  obtain ⟨x,hx,_⟩ := affine_unique_fixed a b
  have hf : (affineTransport G (chosenSlopes G S.colouring) c).along S.walk x = x := (hab x).trans hx
  exact ⟨c,⟨{ regular := hreg, magic := hmag, cycle := persistedCycle S c (hcomp c) x hf }⟩⟩
end XorMagic
