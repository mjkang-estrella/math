import F10B000
import F10B001
import F10B002
import F10B003
import F10B004
import F10B005
import F10B006
import F10B007
import F10B008
import F10B009
import F10B010
import F10B011
import F10B012
import F10B013
import F10B014
import F10B015
import F10B016
import F10B017
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def family10 : RowFamilyTree := (.branch (.branch (.branch (.branch F10B000 F10B001) (.branch F10B002 F10B003)) (.branch (.branch F10B004 F10B005) (.branch F10B006 (.branch F10B007 F10B008)))) (.branch (.branch (.branch F10B009 F10B010) (.branch F10B011 F10B012)) (.branch (.branch F10B013 F10B014) (.branch F10B015 (.branch F10B016 F10B017)))))
theorem F10B000_lift (row : List GridPoint) (h : FamilyMember row F10B000) : FamilyMember row family10 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (h))))
theorem F10B001_lift (row : List GridPoint) (h : FamilyMember row F10B001) : FamilyMember row family10 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (h))))
theorem F10B002_lift (row : List GridPoint) (h : FamilyMember row F10B002) : FamilyMember row family10 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (h))))
theorem F10B003_lift (row : List GridPoint) (h : FamilyMember row F10B003) : FamilyMember row family10 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (h))))
theorem F10B004_lift (row : List GridPoint) (h : FamilyMember row F10B004) : FamilyMember row family10 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (h))))
theorem F10B005_lift (row : List GridPoint) (h : FamilyMember row F10B005) : FamilyMember row family10 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (h))))
theorem F10B006_lift (row : List GridPoint) (h : FamilyMember row F10B006) : FamilyMember row family10 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (h))))
theorem F10B007_lift (row : List GridPoint) (h : FamilyMember row F10B007) : FamilyMember row family10 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h)))))
theorem F10B008_lift (row : List GridPoint) (h : FamilyMember row F10B008) : FamilyMember row family10 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
theorem F10B009_lift (row : List GridPoint) (h : FamilyMember row F10B009) : FamilyMember row family10 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (h))))
theorem F10B010_lift (row : List GridPoint) (h : FamilyMember row F10B010) : FamilyMember row family10 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (h))))
theorem F10B011_lift (row : List GridPoint) (h : FamilyMember row F10B011) : FamilyMember row family10 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (h))))
theorem F10B012_lift (row : List GridPoint) (h : FamilyMember row F10B012) : FamilyMember row family10 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (h))))
theorem F10B013_lift (row : List GridPoint) (h : FamilyMember row F10B013) : FamilyMember row family10 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (h))))
theorem F10B014_lift (row : List GridPoint) (h : FamilyMember row F10B014) : FamilyMember row family10 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (h))))
theorem F10B015_lift (row : List GridPoint) (h : FamilyMember row F10B015) : FamilyMember row family10 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (h))))
theorem F10B016_lift (row : List GridPoint) (h : FamilyMember row F10B016) : FamilyMember row family10 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))
theorem F10B017_lift (row : List GridPoint) (h : FamilyMember row F10B017) : FamilyMember row family10 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
end Polyomino57
