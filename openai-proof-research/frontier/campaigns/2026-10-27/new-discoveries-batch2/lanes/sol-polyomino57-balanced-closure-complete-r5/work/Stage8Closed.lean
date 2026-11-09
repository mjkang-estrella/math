import F8B000Closed
import F8B001Closed
import F8All
set_option autoImplicit false
namespace Polyomino57
theorem stage8_closed (row : List GridPoint) (h : FamilyMember row family8) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  exact h.elim (fun h => F8B000Closed row h) (fun h => F8B001Closed row h)
end Polyomino57
