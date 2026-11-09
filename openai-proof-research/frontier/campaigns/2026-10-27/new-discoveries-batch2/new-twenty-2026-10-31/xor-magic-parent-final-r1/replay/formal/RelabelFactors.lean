import ColourWalks
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
/-- Conjugation of every matching by the same graph isomorphism. -/
def MatchingDecomposition.relabel (F : MatchingDecomposition G d) (e : G ≃g H) :
    MatchingDecomposition H d where
  mate i w := e (F.mate i (e.symm w))
  involutive i w := by simp [F.involutive]
  no_fixed i w := by
    intro h
    have := e.injective (h.trans (e.apply_symm_apply w).symm)
    exact F.no_fixed i (e.symm w) this
  distinct w := by
    intro i j h
    exact F.distinct (e.symm w) (e.injective h)
  cover v w := by
    rw [← e.symm.map_adj_iff, F.cover]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨i,by simpa using congrArg e hi⟩
    · rintro ⟨i,hi⟩; exact ⟨i,by simpa using congrArg e.symm hi⟩

/-- Colour classes and both properness certificates are transported together. -/
def FactorColouring.relabel {F : MatchingDecomposition G d} {hd : 2 ≤ d}
    (b : FactorColouring F hd) (e : G ≃g H) : FactorColouring (F.relabel e) hd where
  colour w := b.colour (e.symm w)
  proper0 w := by simpa [MatchingDecomposition.relabel] using b.proper0 (e.symm w)
  proper1 w := by simpa [MatchingDecomposition.relabel] using b.proper1 (e.symm w)

theorem FactorColouring.directed_relabel {F : MatchingDecomposition G d} {hd : 2 ≤ d}
    (b : FactorColouring F hd) (e : G ≃g H) (u v : W) :
    (b.relabel e).directed u v = b.directed (e.symm u) (e.symm v) := by
  have hm (i : Fin d) : (F.relabel e).mate i u = v ↔ F.mate i (e.symm u) = e.symm v := by
    change e _ = v ↔ _
    exact e.toEquiv.eq_symm_apply.symm
  simp only [FactorColouring.directed, hm]
  rfl
end XorMagic
namespace XorMagic
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
/-- Genuine indexed cycles retain their injection, length, matching membership,
and orientation under relabelling. -/
noncomputable def ColouredCycleData.relabel (C : ColouredCycleData G d) (e : G ≃g H) :
    ColouredCycleData H d where
  factors := C.factors.relabel e
  complementFactors := by
    have hc : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
    let ec : Gᶜ ≃g Hᶜ := {
      toEquiv := e.toEquiv
      map_rel_iff' := by
        intro u v
        change (e u ≠ e v ∧ ¬ H.Adj (e u) (e v)) ↔ (u ≠ v ∧ ¬ G.Adj u v)
        simp only [e.injective.ne_iff, e.map_adj_iff] }
    exact hc ▸ C.complementFactors.relabel ec
  two_le := C.two_le
  length := C.length
  positive := C.positive
  not_three := C.not_three
  cycle i := e (C.cycle i)
  injective := e.injective.comp C.injective
  edges i := by
    simpa [MatchingDecomposition.relabel] using (C.edges i).imp (congrArg e) (congrArg e)
  three_le := C.three_le
  colouring := C.colouring.relabel e
  outgoing i := by
    rw [FactorColouring.directed_relabel]
    simpa using C.outgoing i
end XorMagic
