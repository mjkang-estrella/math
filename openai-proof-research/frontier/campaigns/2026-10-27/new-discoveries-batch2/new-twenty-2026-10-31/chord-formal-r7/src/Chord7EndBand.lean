import Chord7EndLocal
namespace Chord.Round7
open Equiv Model3 Model4 Comb4

/-- Appending an adjacent pair retains the old positions literally. -/
def blockSubdiagram (n : Nat) (hn : 3 ≤ n) :
    Subdiagram (r3Block n hn) (r3Block (n+1) (by omega)) where
  positions i := ⟨i.val, by omega⟩
  increasing := by intro i j h; exact h
  closed i := by apply Fin.ext; rfl

/-- The equal-side face-count clause follows from BandErasure alone. -/
theorem boundary_append_equal (erase : BandErasure) (n) (hn : 3 ≤ n)
    (c : Sides n) (p : Bool) :
    boundary (r3Block (n+1) (by omega)) (appendSides c p p) =
      boundary (r3Block n hn) c + 1 := by
  let D := r3Block (n+1) (by omega)
  let S := blockSubdiagram n hn
  let a : Fin (2*(n+1)) := ⟨2*n, by omega⟩
  have ha : (D.partner a).val = 2*n+1 := by
    change blockMate (2*n) = 2*n+1
    simp [blockMate, show ¬2*n < 3 by omega, show ¬2*n < 6 by omega]
  have hlt : a < D.partner a := by change a.val < (D.partner a).val; rw [ha]; dsimp [a]; omega
  have hp : ∀ i, S.positions i ≠ a := by
    intro i hi
    have hh := congrArg Fin.val hi
    change i.val = 2*n at hh
    have := i.isLt
    omega
  have hc : appendSides c p p a = appendSides c p p (D.partner a) := by
    have he : D.partner a = ⟨2*n+1, by omega⟩ := Fin.ext ha
    simp [a, he, appendSides]
  have hinner : ∀ i, a.val < i.val → i.val < (D.partner a).val →
      appendSides c p p i ≠ appendSides c p p a := by
    intro i hi hj
    rw [ha] at hj
    dsimp [a] at hi
    omega
  have hd := Round6.innermost_distinct D (appendSides c p p) a hlt hc.symm hinner
  have he := Round5.bandErasure_iff_every.mp erase n D (r3Block n hn) S (appendSides c p p) a hp
  have hne : chordDart a ≠ chordDart (D.partner a) := by
    intro h
    exact D.noFixed a (chordDart_injective h).symm
  have hs := (Round6.swap_orbitCount_refined _ (Model2.faceEquiv D (appendSides c p p)) _ _ hne).2 hd
  have hr : restrictSides S (appendSides c p p) = c := by
    funext i
    change appendSides c p p ⟨i.val, by omega⟩ = c i
    simp [appendSides, i.isLt]
  rw [he, hr, ← boundary_eq_orbitCount (by omega) D (appendSides c p p)] at hs
  exact hs.symm

#print axioms boundary_append_equal
end Chord.Round7
