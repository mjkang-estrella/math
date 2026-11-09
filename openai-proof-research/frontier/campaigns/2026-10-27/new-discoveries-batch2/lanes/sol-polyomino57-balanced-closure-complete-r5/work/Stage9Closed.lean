import F9B000Closed
import F9B001Closed
import F9B002Closed
import F9B003Closed
import F9B004Closed
import F9All
set_option autoImplicit false
namespace Polyomino57
theorem stage9_closed (row : List GridPoint) (h : FamilyMember row family9) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  exact h.elim (fun h => h.elim (fun h => F9B000Closed row h) (fun h => F9B001Closed row h)) (fun h => h.elim (fun h => F9B002Closed row h) (fun h => h.elim (fun h => F9B003Closed row h) (fun h => F9B004Closed row h)))
end Polyomino57
