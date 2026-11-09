import ChordModel3Base
namespace Chord.Model3
open Equiv

/-- Generic successor-swap cycle surgery, still an obligation. -/
def SwapCycleLaw : Prop := ∀ size (f : Perm (Fin size)) (a b : Fin size), a ≠ b →
  orbitCount (f * Equiv.swap a b) = orbitCount f + 1 ∨
  orbitCount (f * Equiv.swap a b) + 1 = orbitCount f

/-- The C half-edge at an endpoint. -/
def chordDart {n} (i : Fin (2*n)) : Fin (6*n) := ⟨3*i.val+2, by omega⟩

theorem chordDart_injective {n} : Function.Injective (@chordDart n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [chordDart] at this
  omega

/-- Exact band-erasure normalization, still an obligation. The two endpoints outside
an order embedding constitute the deleted chord. Swapping the two C successors
before suppressing the two bivalent vertices leaves the compressed face orbits.
At n=0 this must give exactly two orbits, the annulus circles. -/
def BandErasure : Prop := ∀ n (D : Diagram (n+1)) (A : Diagram n)
  (S : Subdiagram A D) (c : Sides (n+1)),
  ∃ p : Fin (2*(n+1)), (∀ i, S.positions i ≠ p) ∧
    orbitCount (Model2.faceEquiv D c *
      Equiv.swap (chordDart p) (chordDart (D.partner p))) =
    boundary A (restrictSides S c)

/-- The surgery obligations imply the literal frozen Deletion Prop. -/
theorem deletion_of_surgery (swapLaw : SwapCycleLaw) (erase : BandErasure) : Deletion := by
  intro n D A S c
  obtain ⟨p, _, hp⟩ := erase n D A S c
  have hne : chordDart p ≠ chordDart (D.partner p) := by
    intro h
    exact D.noFixed p (chordDart_injective h).symm
  have hs := swapLaw _ (Model2.faceEquiv D c) _ _ hne
  rw [hp, ← boundary_eq_orbitCount (by omega) D c] at hs
  exact hs

/-- Both dependent model targets follow once the two surgery obligations close. -/
theorem consequences_of_surgery (swapLaw : SwapCycleLaw) (erase : BandErasure) :
    Deletion ∧ EulerRealization ∧ Heredity :=
  ⟨deletion_of_surgery swapLaw erase,
    Model2.euler_of_deletion (deletion_of_surgery swapLaw erase),
    Model2.heredity_of_deletion (deletion_of_surgery swapLaw erase)⟩
end Chord.Model3
