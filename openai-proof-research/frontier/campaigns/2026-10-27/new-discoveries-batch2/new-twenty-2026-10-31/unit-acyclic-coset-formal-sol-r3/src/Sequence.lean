import Controls
noncomputable section
namespace UnitCoset
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {C D : Finset G}
theorem sequence_length (f : C ≃ D) : (sequence f).length = (support f).card := by
  simp [sequence]
theorem sequence_decreasing (f : C ≃ D) : (sequence f).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _
theorem sequence_multiset (f : C ≃ D) :
    (sequence f : Multiset ℕ) = (support f).val.map (multiplicity f) := by
  simp [sequence]
theorem unit_iff_replicate (f : C ≃ D) :
    UnitSequence f ↔ sequence f = List.replicate (support f).card 1 := by
  simp only [List.eq_replicate_iff, sequence_length, true_and]
  rfl
omit [DecidableEq G] in
theorem source_disjoint_bridge (C D : Finset G) :
    (∀ a ∈ C, ∀ b ∈ D, a + b ∉ C) ↔
    Disjoint (↑C : Set G) {x | ∃ a ∈ C, ∃ b ∈ D, a + b = x} := by
  rw [Set.disjoint_left]
  constructor
  · intro h x hx ⟨a, ha, b, hb, he⟩
    exact h a ha b hb (he.symm ▸ hx)
  · intro h a ha b hb hab
    exact h hab ⟨a, ha, b, hb, rfl⟩
end UnitCoset
