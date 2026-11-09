import ChordComb4Innermost
namespace Chord.Comb4

/-- The endpoint set remaining after one chord is removed. -/
def keptAfter {n} (D : Diagram (n+1)) (a : Fin (2*(n+1))) :
    Finset (Fin (2*(n+1))) := Finset.univ \ {a,D.partner a}

theorem keptAfter_card {n} (D : Diagram (n+1)) (a) :
    (keptAfter D a).card = 2*n := by
  have h := D.noFixed a
  simp [keptAfter, Finset.card_sdiff, Finset.card_pair (Ne.symm h)]
  omega

theorem keptAfter_closed {n} (D : Diagram (n+1)) (a) :
    ∀ i ∈ keptAfter D a, D.partner i ∈ keptAfter D a := by
  intro i hi
  simp only [keptAfter, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_and, not_or] at hi ⊢
  constructor
  · intro h
    have hh := congrArg D.partner h
    rw [D.involutive] at hh
    exact hi.2 hh
  · intro h
    have hh := congrArg D.partner h
    simp only [D.involutive] at hh
    exact hi.1 hh

def removeChord {n} (D : Diagram (n+1)) (a : Fin (2*(n+1))) : Diagram n :=
  compress D (keptAfter D a) (keptAfter_card D a) (keptAfter_closed D a)

def removeChordSubdiagram {n} (D : Diagram (n+1)) (a) :
    Subdiagram (removeChord D a) D :=
  compression D (keptAfter D a) (keptAfter_card D a) (keptAfter_closed D a)

/-- UNPROVED refined face-splitting obligation, rather than the weaker ±1
Deletion Prop. It is restricted to a monochromatic innermost chord and the
actual frozen boundary function. -/
def MonochromaticSplit : Prop := ∀ n (D : Diagram (n+1)) (c : Sides (n+1)) a,
  a < D.partner a → (∀ i, c (D.partner i) = c i) →
  (∀ i, a < i → i < D.partner a → c i ≠ c a) →
  boundary D c = boundary (removeChord D a)
    (restrictSides (removeChordSubdiagram D a) c) + 1

/-- Once the exact split case is supplied, the innermost argument proves the
full boundary equation, not just the existence of a genus-zero thickening. -/
theorem boundary_of_bipartite (split : MonochromaticSplit) :
    ∀ n (D : Diagram n) (c : Sides n),
    (∀ i, c (D.partner i) = c i) →
    (∀ a b, Crosses D a b → c a ≠ c b) → boundary D c = n+2 := by
  intro n
  induction n with
  | zero => intro D c _ _; exact empty_boundary D c
  | succ n ih =>
    intro D c hc hx
    let z : Fin (2*(n+1)) := ⟨0,by omega⟩
    have hz : z < D.partner z := by
      have hne := D.noFixed z
      have hval : (D.partner z).val ≠ 0 := fun h => hne (Fin.ext h)
      change 0 < (D.partner z).val
      omega
    obtain ⟨a,ha,he,hinner⟩ := innermost_monochromatic D c hc hx (c z) ⟨z,hz,rfl⟩
    let S := removeChordSubdiagram D a
    have hc' : ∀ i, restrictSides S c ((removeChord D a).partner i) = restrictSides S c i := by
      intro i
      change c (S.positions ((removeChord D a).partner i)) = c (S.positions i)
      rw [← S.closed]
      exact hc _
    have hx' : ∀ i j, Crosses (removeChord D a) i j → restrictSides S c i ≠ restrictSides S c j := by
      intro i j hij
      exact hx _ _ ((crosses_iff S i j).mpr hij)
    have hb := ih (removeChord D a) (restrictSides S c) hc' hx'
    have hs := split n D c a ha hc (by simpa only [he] using hinner)
    change boundary D c = boundary (removeChord D a) (restrictSides S c) + 1 at hs
    omega

theorem planarity_of_split (split : MonochromaticSplit) : BipartitePlanarity := by
  intro n D h
  obtain ⟨c,hc,hx⟩ := h
  refine ⟨c,?_⟩
  unfold HasGenus
  rw [boundary_of_bipartite split n D c hc hx]
  omega
end Chord.Comb4
