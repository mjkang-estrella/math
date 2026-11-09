import TreeBlock066
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B066L0 : RowFamilyTree := TreeBlock066L0
abbrev F11B066L1 : RowFamilyTree := TreeBlock066L1
abbrev F11B066L2 : RowFamilyTree := TreeBlock066L2
abbrev F11B066L3 : RowFamilyTree := TreeBlock066L3
abbrev F11B066 : RowFamilyTree := TreeBlock066
theorem F11B066L0_lift (row : List GridPoint) (h : FamilyMember row F11B066L0) : FamilyMember row F11B066 := by
  exact Or.inl (Or.inl (h))
theorem F11B066L1_lift (row : List GridPoint) (h : FamilyMember row F11B066L1) : FamilyMember row F11B066 := by
  exact Or.inl (Or.inr (h))
theorem F11B066L2_lift (row : List GridPoint) (h : FamilyMember row F11B066L2) : FamilyMember row F11B066 := by
  exact Or.inr (Or.inl (h))
theorem F11B066L3_lift (row : List GridPoint) (h : FamilyMember row F11B066L3) : FamilyMember row F11B066 := by
  exact Or.inr (Or.inr (h))
end Polyomino57
