import InterpEndpoints
import ChosenSeedLiftData
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
/-- The complement factors required by the chosen lift are supplied by the
three disjoint block families, for every translation. -/
noncomputable def ColouredSeed.complementInput {closed : Bool}
    (S : ColouredSeed G n d closed) (c : OrientedEdge G → Four) :
    LiftComplementInput G (chosenSlopes G S.colouring) c d := by
  have hcard : d+1 ≤ m := by
    have hm : Nonempty (Fin m) := by
      have h := S.seed.magic
      cases closed <;> exact h.1.nonempty
    obtain ⟨v⟩ := hm
    have hh := G.degree_lt_card_verts v
    rw [S.seed.regular v] at hh
    simpa using hh
  refine ⟨?_⟩
  have h := (affineTransport G (chosenSlopes G S.colouring) c).complementMatching_exact
    S.seed.factorCycle.factors S.seed.factorCycle.complementFactors (by simpa using hcard)
  simpa [Fintype.card_prod, Fintype.card_fin, show Fintype.card Four = 4 by decide,
    Nat.mul_comm] using h

/-- Product-type assembly with no complement hypothesis remaining. -/
theorem chosen_seed_product [Nonempty (Fin m)] {closed : Bool}
    (S : ColouredSeed G n d closed) (hd : 4 ≤ d)
    (hparity : if closed then Even d else Odd d) :
    ∃ c : OrientedEdge G → Four,
      Nonempty (ColouredLiftSeed (affineTransport G (chosenSlopes G S.colouring) c).graph
        (n+2) d closed) :=
  chosen_seed_lift_data S hd hparity S.complementInput
end XorMagic
