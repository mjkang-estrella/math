import SupportData165
import SignedSupport165_000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport165
theorem verified : ∀ A ∈ signedCatalogue 509765795185217760 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl
  · exact checked0 A hm
end Nut8.FiniteSupport165
