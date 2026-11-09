import ColourOrientation
import LiftOrientedCycle
namespace XorMagic
/-- A seed with a colouring and a genuine oriented distinguished cycle.
The indexed cycle and walk are tied vertex by vertex. -/
structure ColouredSeed {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (n d : ℕ) (closed : Bool) where
  seed : LiftSeed G n d closed
  strong : 3 ≤ seed.factorCycle.length
  colouring : FactorColouring seed.factorCycle.factors seed.factorCycle.two_le
  walk : G.Walk (seed.factorCycle.cycle ⟨0,seed.factorCycle.positive⟩)
    (seed.factorCycle.cycle ⟨0,seed.factorCycle.positive⟩)
  isCycle : walk.IsCycle
  length_eq : walk.length = seed.factorCycle.length
  indexed : ∀ i : Fin seed.factorCycle.length, walk.getVert i.val = seed.factorCycle.cycle i
  starts_true : colouring.colour (seed.factorCycle.cycle ⟨0,seed.factorCycle.positive⟩) = true
  oriented : OmegaWalk G (chosenSlopes G colouring) walk

def ColouredSeed.strongCycle {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {closed : Bool} (S : ColouredSeed G n d closed) : StrongFactorCycleData G d where
  toFactorCycleData := S.seed.factorCycle
  three_le := S.strong

/-- Projection preserves proper colouring on both lifted factors. -/
def FactorColouring.lift {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} {F : MatchingDecomposition G d} {hd : 2 ≤ d}
    (b : FactorColouring F hd) (T : EdgeTransport G) : FactorColouring (T.matching F) hd where
  colour p := b.colour p.1
  proper0 p := b.proper0 p.1
  proper1 p := b.proper1 p.1
end XorMagic
