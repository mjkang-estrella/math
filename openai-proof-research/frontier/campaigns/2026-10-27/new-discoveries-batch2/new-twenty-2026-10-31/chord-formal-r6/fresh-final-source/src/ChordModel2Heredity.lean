import ChordModel2Subdiagram
import Mathlib.Order.Preorder.Finite
namespace Chord.Model2

def emptyDiagram : Diagram 0 where
  partner i := Fin.elim0 i
  involutive i := Fin.elim0 i
  noFixed i := Fin.elim0 i

def emptySubdiagram {n} (D : Diagram n) : Subdiagram emptyDiagram D where
  positions i := Fin.elim0 i
  increasing := by intro i; exact Fin.elim0 i
  closed i := Fin.elim0 i

/-- No arithmetic parity argument is needed once the exact deletion law is known. -/
theorem euler_of_deletion (del : Deletion) : EulerRealization := by
  intro n
  induction n with
  | zero => intro D c; exact ⟨0, rfl⟩
  | succ n ih =>
    intro D c
    obtain ⟨B, _, ⟨U⟩, _⟩ := factor_one (emptySubdiagram D) (by omega)
    obtain ⟨g, hg⟩ := ih B (restrictSides U c)
    have hd := del n D B U c
    unfold HasGenus at hg ⊢
    rcases hd with hd | hd
    · exact ⟨g+1, by omega⟩
    · exact ⟨g, by omega⟩

theorem subdiagram_same_size {n} {A D : Diagram n} (S : Subdiagram A D) : A = D := by
  have hp := S.increasing.eq_id
  have he : A.partner = D.partner := by
    funext i
    have h := S.closed i
    simpa only [hp, id_eq] using h.symm
  cases A
  cases D
  cases he
  rfl

/-- Genus under a single deletion is unchanged or decreases by one. -/
theorem genus_delete (del : Deletion) {n} (D : Diagram (n+1)) (A : Diagram n)
    (S : Subdiagram A D) (c : Sides (n+1)) (g h : Nat)
    (hg : HasGenus D c g) (hh : HasGenus A (restrictSides S c) h) :
    h = g ∨ h+1 = g := by
  have hd := del n D A S c
  unfold HasGenus at hg hh
  rcases hd with hd | hd <;> omega

/-- Iteration through actual single deletions, with side assignments extended at each step. -/
theorem heredity_of_deletion (del : Deletion) : Heredity := by
  have euler := euler_of_deletion del
  intro k n
  induction n with
  | zero =>
    intro A D S hD
    have hk := subdiagram_size S
    have hk0 : k = 0 := by omega
    subst k
    rw [subdiagram_same_size S]
    exact hD
  | succ n ih =>
    intro A D S hD
    have hk := subdiagram_size S
    by_cases he : k = n+1
    · subst k
      rw [subdiagram_same_size S]
      exact hD
    · obtain ⟨B, ⟨T⟩, ⟨U⟩, _⟩ := factor_one S (by omega)
      apply ih A B T
      intro g hg
      obtain ⟨a, ha⟩ := hg
      obtain ⟨c, hc⟩ := sides_extend U a
      obtain ⟨h, hh⟩ := euler (n+1) D c
      have hbound := hD h ⟨c, hh⟩
      rw [← hc] at ha
      have hg_le := genus_delete del D B U c h g hh ha
      omega
end Chord.Model2
