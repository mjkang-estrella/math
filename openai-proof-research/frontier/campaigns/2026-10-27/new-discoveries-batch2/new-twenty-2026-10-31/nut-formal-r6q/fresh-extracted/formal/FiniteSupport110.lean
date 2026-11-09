import SupportData110
import SignedSupport110_000
import SignedSupport110_001
import SignedSupport110_002
import SignedSupport110_003
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport110
theorem verified : ∀ A ∈ signedCatalogue 1013598299868930112 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked0 A hm
  · exact checked1 A hm
  · exact checked2 A hm
  · exact checked3 A hm
  · exact checked4 A hm
  · exact checked5 A hm
  · exact checked6 A hm
  · exact checked7 A hm
  · exact checked8 A hm
  · exact checked9 A hm
  · exact checked10 A hm
  · exact checked11 A hm
  · exact checked12 A hm
  · exact checked13 A hm
  · exact checked14 A hm
end Nut8.FiniteSupport110
