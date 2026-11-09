import SupportData072
import SignedSupport072_000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport072
theorem verified : ∀ A ∈ signedCatalogue 2530044735819653248 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl
  · exact checked0 A hm
  · exact checked1 A hm
end Nut8.FiniteSupport072
