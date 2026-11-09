import SupportData122
import SignedSupport122_000
import SignedSupport122_001
import SignedSupport122_002
import SignedSupport122_003
import SignedSupport122_004
import SignedSupport122_005
import SignedSupport122_006
import SignedSupport122_007
import SignedSupport122_008
import SignedSupport122_009
import SignedSupport122_010
import SignedSupport122_011
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport122
theorem verified : ∀ A ∈ signedCatalogue 217591204463812800 e p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  intro A hm
  obtain ⟨U, hU, hm⟩ := Finset.mem_biUnion.mp hm
  rw [unsigned_enumeration] at hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact checked34 A hm
  · exact checked35 A hm
  · exact checked36 A hm
  · exact checked37 A hm
  · exact checked38 A hm
  · exact checked39 A hm
  · exact checked40 A hm
  · exact checked41 A hm
  · exact checked42 A hm
  · exact checked43 A hm
  · exact checked44 A hm
  · exact checked45 A hm
  · exact checked46 A hm
end Nut8.FiniteSupport122
