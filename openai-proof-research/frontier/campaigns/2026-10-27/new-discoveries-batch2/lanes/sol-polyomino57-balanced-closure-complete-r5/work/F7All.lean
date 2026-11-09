import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def family7 : RowFamilyTree := F7B000
theorem F7B000_lift (row : List GridPoint) (h : FamilyMember row F7B000) : FamilyMember row family7 := by
  exact h
end Polyomino57
