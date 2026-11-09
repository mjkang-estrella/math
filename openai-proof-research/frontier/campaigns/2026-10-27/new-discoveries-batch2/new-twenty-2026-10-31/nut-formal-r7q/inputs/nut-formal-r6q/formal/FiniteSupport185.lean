import SupportData185
import SignedSupport185_000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport185
theorem verified : ∀ A ∈ signedCatalogue 1885412478031085572 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl
  · exact checked0 A hm
  · exact checked1 A hm
end Nut8.FiniteSupport185
