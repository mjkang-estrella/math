import Sequence
namespace Independent
open UnitCoset
theorem literal_refutation :
    ¬ (∀ (G : Type) [AddCommGroup G] [DecidableEq G] (C D : Finset G),
      C.Nonempty → D.Nonempty → C.card = D.card → 0 ∉ D →
      Disjoint (↑C : Set G) {x | ∃ a ∈ C, ∃ b ∈ D, a + b = x} →
      ∃ f : C ≃ D, Admissible C D f ∧
        sequence f = List.replicate (support f).card 1 ∧ Acyclic f) := by
  intro h
  apply refutation
  intro G _ _ C D hs
  obtain ⟨f, ha, hu, hc⟩ := h G C D hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    ((source_disjoint_bridge C D).mp hs.2.2.2.2)
  exact ⟨f, ha, (unit_iff_replicate f).mpr hu, hc⟩
#print literal_refutation
#print axioms literal_refutation
end Independent
