import ChordModel4Erasure
namespace Chord.Model4
open Equiv Model3

/-- The edge involution sends a chord half-edge to its paired half-edge. -/
theorem theta_chordDart {n} (D : Diagram n) (p : Fin (2*n)) :
    theta D (chordDart p).val = (chordDart (D.partner p)).val := by
  simp only [chordDart, theta]
  rw [show (3*p.val+2)/3 = p.val by omega,
    show (3*p.val+2)%3 = 2 by omega]
  simp only [mate, dite_eq_left p.isLt]

/-- Swapping the C successors replaces the deleted chord's two edge flips by
fixed points; all other edge flips are unchanged. This is the local algebra
before suppressing the two bivalent backbone vertices. -/
theorem erased_face_formula {n} (D : Diagram n) (c : Sides n)
    (p : Fin (2*n)) (x : Fin (6*n)) :
    ((Model2.faceEquiv D c * swap (chordDart p) (chordDart (D.partner p))) x).val =
      rho c (if x = chordDart p ∨ x = chordDart (D.partner p)
        then x.val else theta D x.val) := by
  by_cases hp : x = chordDart p
  · subst x
    rw [ite_eq_left (Or.inl rfl)]
    change (Model2.faceEquiv D c (swap (chordDart p) (chordDart (D.partner p)) (chordDart p))).val = _
    rw [swap_apply_left]
    change rho c (theta D (chordDart (D.partner p)).val) = _
    rw [theta_chordDart, D.involutive]
  · by_cases hq : x = chordDart (D.partner p)
    · subst x
      rw [ite_eq_left (Or.inr rfl)]
      change (Model2.faceEquiv D c (swap (chordDart p) (chordDart (D.partner p)) (chordDart (D.partner p)))).val = _
      rw [swap_apply_right]
      change rho c (theta D (chordDart p).val) = _
      rw [theta_chordDart]
    · rw [ite_eq_right (not_or.mpr ⟨hp, hq⟩)]
      change (Model2.faceEquiv D c (swap (chordDart p) (chordDart (D.partner p)) x)).val = _
      rw [swap_apply_of_ne_of_ne hp hq]
      rfl
end Chord.Model4
