import ColourWalks
namespace XorMagic
variable {m d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {F : MatchingDecomposition G d} {hd : 2 ≤ d}
/-- A vertex-by-vertex directed-edge certificate suffices for OmegaWalk. -/
theorem omegaWalk_of_steps (b : FactorColouring F hd) {u v : Fin m} (p : G.Walk u v)
    (h : ∀ i, i < p.length → b.directed (p.getVert i) (p.getVert (i+1)) = 1) :
    OmegaWalk G (chosenSlopes G b) p := by
  induction p with
  | nil => trivial
  | @cons u v w ha p ih =>
    constructor
    · rw [chosen_outgoing G b ha]
      simpa only [SimpleGraph.Walk.getVert, SimpleGraph.Walk.getVert_zero] using h 0 (by simp)
    · apply ih
      intro i hi
      exact h (i+1) (by simpa using Nat.succ_lt_succ hi)
end XorMagic
