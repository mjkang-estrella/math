import F10B000Closed
import F10B001Closed
import F10B002Closed
import F10B003Closed
import F10B004Closed
import F10B005Closed
import F10B006Closed
import F10B007Closed
import F10B008Closed
import F10B009Closed
import F10B010Closed
import F10B011Closed
import F10B012Closed
import F10B013Closed
import F10B014Closed
import F10B015Closed
import F10B016Closed
import F10B017Closed
import F10All
set_option autoImplicit false
namespace Polyomino57
theorem stage10_closed (row : List GridPoint) (h : FamilyMember row family10) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  exact h.elim (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => F10B000Closed row h) (fun h => F10B001Closed row h)) (fun h => h.elim (fun h => F10B002Closed row h) (fun h => F10B003Closed row h))) (fun h => h.elim (fun h => h.elim (fun h => F10B004Closed row h) (fun h => F10B005Closed row h)) (fun h => h.elim (fun h => F10B006Closed row h) (fun h => h.elim (fun h => F10B007Closed row h) (fun h => F10B008Closed row h))))) (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => F10B009Closed row h) (fun h => F10B010Closed row h)) (fun h => h.elim (fun h => F10B011Closed row h) (fun h => F10B012Closed row h))) (fun h => h.elim (fun h => h.elim (fun h => F10B013Closed row h) (fun h => F10B014Closed row h)) (fun h => h.elim (fun h => F10B015Closed row h) (fun h => h.elim (fun h => F10B016Closed row h) (fun h => F10B017Closed row h)))))
end Polyomino57
