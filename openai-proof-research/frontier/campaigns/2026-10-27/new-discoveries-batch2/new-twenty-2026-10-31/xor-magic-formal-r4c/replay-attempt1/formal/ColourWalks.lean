import ColouredSeed
namespace XorMagic
variable {m d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
variable {F : MatchingDecomposition G d} {hd : 2 ≤ d} (b : FactorColouring F hd)
theorem omegaWalk_step {u v : Fin m} (p : G.Walk u v)
    (h : OmegaWalk G (chosenSlopes G b) p) {i : ℕ} (hi : i < p.length) :
    b.directed (p.getVert i) (p.getVert (i+1)) = 1 := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons u v w ha p ih =>
    cases i with
    | zero => simpa only [SimpleGraph.Walk.getVert, SimpleGraph.Walk.getVert_zero] using (chosen_outgoing G b ha).symm.trans h.1
    | succ i => exact ih h.2 (by simpa using hi)

variable {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
variable {e : ℕ} {D : MatchingDecomposition H e} {he : 2 ≤ e}
/-- Directed colours lift on every actual edge, not just distinguished edges. -/
theorem FactorColouring.directed_lift (a : FactorColouring D he) (T : EdgeTransport H)
    {p q : V × Four} (hpq : T.graph.Adj p q) :
    (a.lift T).directed p q = a.directed p.1 q.1 := by
  have hm (i : Fin e) : (T.matching D).mate i p = q ↔ D.mate i p.1 = q.1 := by
    constructor
    · intro h; exact congrArg Prod.fst h
    · intro h
      apply Prod.ext h
      change T.map p.1 (D.mate i p.1) p.2 = q.2
      rw [h]; exact hpq.2
  simp only [FactorColouring.directed, hm]
  rfl

/-- Indexed oriented cycles, usable before and after lifting and relabelling. -/
structure ColouredCycleData (H : SimpleGraph V) (e : ℕ) extends StrongFactorCycleData H e where
  colouring : FactorColouring factors two_le
  outgoing : ∀ i, colouring.directed (cycle i)
    (cycle ⟨(i.val+1)%length, Nat.mod_lt _ positive⟩) = 1

omit e in
/-- Bridge from the certified walk to the inherited indexed cycle. -/
def ColouredSeed.colouredCycle {n : ℕ} {closed : Bool} (S : ColouredSeed G n d closed) :
    ColouredCycleData G d where
  toStrongFactorCycleData := S.strongCycle
  colouring := S.colouring
  outgoing i := by
    dsimp [ColouredSeed.strongCycle] at i ⊢
    have hs := omegaWalk_step S.colouring S.walk S.oriented (i := i.val) (by rw [S.length_eq]; exact i.isLt)
    rw [S.indexed i] at hs
    by_cases hi : i.val+1 < S.seed.factorCycle.length
    · have hm : (i.val+1)%S.seed.factorCycle.length = i.val+1 := Nat.mod_eq_of_lt hi
      have he := S.indexed ⟨i.val+1,hi⟩
      rw [he] at hs
      simpa only [hm] using hs
    · have he : i.val+1 = S.seed.factorCycle.length := by have := i.isLt; omega
      have hg : S.walk.getVert (i.val+1) = S.seed.factorCycle.cycle ⟨0,S.seed.factorCycle.positive⟩ := by
        simpa only [← S.length_eq, he] using (SimpleGraph.Walk.getVert_length S.walk)
      rw [hg] at hs
      simpa only [he, Nat.mod_self] using hs
end XorMagic
