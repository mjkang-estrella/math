import SupportData123
import SignedSupport123_000
import SignedSupport123_001
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport123
theorem verified : ∀ A ∈ signedCatalogue 4865306019910164672 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked0 A hm
  · exact checked1 A hm
  · exact checked2 A hm
  · exact checked3 A hm
  · exact checked4 A hm
  · exact checked5 A hm
  · exact checked6 A hm
  · exact checked7 A hm
end Nut8.FiniteSupport123
