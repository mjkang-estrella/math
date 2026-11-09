import F8B000
import F8B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def family8 : RowFamilyTree := (.branch F8B000 F8B001)
theorem F8B000_lift (row : List GridPoint) (h : FamilyMember row F8B000) : FamilyMember row family8 := by
  exact Or.inl (h)
theorem F8B001_lift (row : List GridPoint) (h : FamilyMember row F8B001) : FamilyMember row family8 := by
  exact Or.inr (h)
end Polyomino57
