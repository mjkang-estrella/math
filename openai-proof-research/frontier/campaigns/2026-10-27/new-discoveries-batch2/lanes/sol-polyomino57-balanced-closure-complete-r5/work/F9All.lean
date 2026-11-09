import F9B000
import F9B001
import F9B002
import F9B003
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def family9 : RowFamilyTree := (.branch (.branch F9B000 F9B001) (.branch F9B002 (.branch F9B003 F9B004)))
theorem F9B000_lift (row : List GridPoint) (h : FamilyMember row F9B000) : FamilyMember row family9 := by
  exact Or.inl (Or.inl (h))
theorem F9B001_lift (row : List GridPoint) (h : FamilyMember row F9B001) : FamilyMember row family9 := by
  exact Or.inl (Or.inr (h))
theorem F9B002_lift (row : List GridPoint) (h : FamilyMember row F9B002) : FamilyMember row family9 := by
  exact Or.inr (Or.inl (h))
theorem F9B003_lift (row : List GridPoint) (h : FamilyMember row F9B003) : FamilyMember row family9 := by
  exact Or.inr (Or.inr (Or.inl (h)))
theorem F9B004_lift (row : List GridPoint) (h : FamilyMember row F9B004) : FamilyMember row family9 := by
  exact Or.inr (Or.inr (Or.inr (h)))
end Polyomino57
