import SupportData034
import SignedSupport034_000
import SignedSupport034_001
import SignedSupport034_002
import SignedSupport034_003
import SignedSupport034_004
import SignedSupport034_005
import SignedSupport034_006
import SignedSupport034_007
import SignedSupport034_008
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport034
theorem verified : ∀ A ∈ signedCatalogue 363124883340673152 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact checked15 A hm
  · exact checked16 A hm
  · exact checked17 A hm
  · exact checked18 A hm
  · exact checked19 A hm
  · exact checked20 A hm
  · exact checked21 A hm
  · exact checked22 A hm
  · exact checked23 A hm
  · exact checked24 A hm
  · exact checked25 A hm
  · exact checked26 A hm
  · exact checked27 A hm
  · exact checked28 A hm
  · exact checked29 A hm
  · exact checked30 A hm
  · exact checked31 A hm
  · exact checked32 A hm
  · exact checked33 A hm
end Nut8.FiniteSupport034
