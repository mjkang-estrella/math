import ChordModel3Transport
namespace Chord.Model3

/-- Deletion of the last band includes the two empty annulus circles. -/
theorem deletion_zero (D : Diagram 1) (A : Diagram 0)
    (S : Subdiagram A D) (c : Sides 1) :
    boundary A (restrictSides S c) = boundary D c+1 ∨
    boundary A (restrictSides S c)+1 = boundary D c := by
  have hb := one_boundary_values c
  rw [← classify_one D] at hb
  have ha := empty_boundary A (restrictSides S c)
  omega

/-- Exact restriction to each two-position order embedding, checked in the kernel. -/
private theorem deletion_two_u2 : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, u2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2,
    boundary one (c ∘ p) = boundary u2 c+1 ∨
    boundary one (c ∘ p)+1 = boundary u2 c := by decide
private theorem deletion_two_r2 : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, r2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2,
    boundary one (c ∘ p) = boundary r2 c+1 ∨
    boundary one (c ∘ p)+1 = boundary r2 c := by decide
private theorem deletion_two_nested : ∀ p : Fin 2 → Fin 4,
    StrictMono p → (∀ i, nested2.partner (p i) = p (one.partner i)) →
    ∀ c : Sides 2,
    boundary one (c ∘ p) = boundary nested2 c+1 ∨
    boundary one (c ∘ p)+1 = boundary nested2 c := by decide

/-- Single deletion holds for all two-chord diagrams and all side restrictions. -/
theorem deletion_one (D : Diagram 2) (A : Diagram 1)
    (S : Subdiagram A D) (c : Sides 2) :
    boundary A (restrictSides S c) = boundary D c+1 ∨
    boundary A (restrictSides S c)+1 = boundary D c := by
  have ha := classify_one A
  subst A
  rcases classify_two D with hd | hd | hd <;> subst D
  · exact deletion_two_u2 S.positions S.increasing S.closed c
  · exact deletion_two_r2 S.positions S.increasing S.closed c
  · exact deletion_two_nested S.positions S.increasing S.closed c
end Chord.Model3
