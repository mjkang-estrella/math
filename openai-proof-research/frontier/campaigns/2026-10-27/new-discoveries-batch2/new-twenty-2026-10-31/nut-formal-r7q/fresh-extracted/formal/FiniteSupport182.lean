import SupportData182
import SignedSupport182_000
import SignedSupport182_001
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport182
theorem verified : ∀ A ∈ signedCatalogue 3545125517269812360 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl
  · exact checked0 A hm
  · exact checked1 A hm
  · exact checked2 A hm
  · exact checked3 A hm
  · exact checked4 A hm
end Nut8.FiniteSupport182
