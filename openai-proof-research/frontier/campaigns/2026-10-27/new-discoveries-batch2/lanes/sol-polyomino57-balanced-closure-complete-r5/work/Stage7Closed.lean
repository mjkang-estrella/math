import F7B000Closed
import F7All
set_option autoImplicit false
namespace Polyomino57
theorem stage7_closed (row : List GridPoint) (h : FamilyMember row family7) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  exact F7B000Closed row h
end Polyomino57
