import ChordModel4Swap
namespace Chord.Model4
open Equiv Model3

/-- A retraction plus local orbit steps certifies a simultaneous suppression. -/
theorem orbitCount_of_retraction {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α → β) (r : β → α)
    (hretract : ∀ x, r (e x) = x)
    (he : ∀ x, Perm.SameCycle g (e x) (e (f x)))
    (hr : ∀ y, Perm.SameCycle f (r y) (r (g y)))
    (hmeet : ∀ y, Perm.SameCycle g (e (r y)) y) :
    orbitCount f = orbitCount g := by
  apply orbitCount_of_section f g e
  · intro x y
    constructor
    · exact sameCycle_map f g e he
    · intro h
      simpa only [hretract] using sameCycle_map g f r hr h
  · intro y; exact ⟨r y, hmeet y⟩

private theorem erasure_one_check : ∀ c : Sides 1,
    cycles 6 (Model2.rawPerm (Model2.faceEquiv one c *
      swap (chordDart ⟨0, by decide⟩) (chordDart (one.partner ⟨0, by decide⟩)))) = 2 := by decide

/-- Band erasure is unconditional for deletion of the last chord. -/
theorem bandErasure_zero (D : Diagram 1) (A : Diagram 0)
    (S : Subdiagram A D) (c : Sides 1) :
    ∃ p : Fin 2, (∀ i, S.positions i ≠ p) ∧
      orbitCount (Model2.faceEquiv D c * swap (chordDart p) (chordDart (D.partner p))) =
        boundary A (restrictSides S c) := by
  have hd := classify_one D
  subst D
  refine ⟨⟨0, by decide⟩, (fun i => Fin.elim0 i), ?_⟩
  rw [empty_boundary, ← cycles_eq_orbitCount]
  exact erasure_one_check c

private theorem erasure_two_u2 : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, u2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2, ∃ x : Fin 4, (∀ i, p i ≠ x) ∧
      cycles 12 (Model2.rawPerm (Model2.faceEquiv u2 c *
        swap (chordDart x) (chordDart (u2.partner x)))) = boundary one (c ∘ p) := by decide
private theorem erasure_two_r2 : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, r2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2, ∃ x : Fin 4, (∀ i, p i ≠ x) ∧
      cycles 12 (Model2.rawPerm (Model2.faceEquiv r2 c *
        swap (chordDart x) (chordDart (r2.partner x)))) = boundary one (c ∘ p) := by decide
private theorem erasure_two_nested : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, nested2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2, ∃ x : Fin 4, (∀ i, p i ≠ x) ∧
      cycles 12 (Model2.rawPerm (Model2.faceEquiv nested2 c *
        swap (chordDart x) (chordDart (nested2.partner x)))) = boundary one (c ∘ p) := by decide

/-- The exact surgery identity also holds for every two-chord diagram. -/
theorem bandErasure_one (D : Diagram 2) (A : Diagram 1)
    (S : Subdiagram A D) (c : Sides 2) :
    ∃ p : Fin 4, (∀ i, S.positions i ≠ p) ∧
      orbitCount (Model2.faceEquiv D c * swap (chordDart p) (chordDart (D.partner p))) =
        boundary A (restrictSides S c) := by
  have ha := classify_one A
  subst A
  have h : ∃ p : Fin 4, (∀ i, S.positions i ≠ p) ∧
      cycles 12 (Model2.rawPerm (Model2.faceEquiv D c *
        swap (chordDart p) (chordDart (D.partner p)))) = boundary one (c ∘ S.positions) := by
    rcases classify_two D with hd | hd | hd <;> subst D
    · exact erasure_two_u2 S.positions S.increasing S.closed c
    · exact erasure_two_r2 S.positions S.increasing S.closed c
    · exact erasure_two_nested S.positions S.increasing S.closed c
  simpa only [cycles_eq_orbitCount, restrictSides] using h

/-- Only band erasure remains in the model surgery route. -/
theorem deletion_of_bandErasure (erase : BandErasure) : Deletion :=
  deletion_of_surgery swapCycleLaw_proved erase

theorem euler_of_bandErasure (erase : BandErasure) : EulerRealization :=
  Model2.euler_of_deletion (deletion_of_bandErasure erase)

theorem heredity_of_bandErasure (erase : BandErasure) : Heredity :=
  Model2.heredity_of_deletion (deletion_of_bandErasure erase)
end Chord.Model4
