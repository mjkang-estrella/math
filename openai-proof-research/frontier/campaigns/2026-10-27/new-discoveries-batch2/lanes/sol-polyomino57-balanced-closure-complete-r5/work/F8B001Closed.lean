import C8R02048
import C8R02080
import C8R02112
import C8R02144
import C8R02176
import C8R02208
import C8R02240
import C8R02272
import C8R02304
import C8R02336
import C8R02368
import C8R02400
import C8R02432
import C8R02464
import C8R02496
import C8R02528
import C8R02560
import C8R02592
import C8R02624
import C8R02656
import C8R02688
import C8R02720
set_option autoImplicit false
namespace Polyomino57
theorem F8B001Closed (row : List GridPoint) (h : FamilyMember row F8B001) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  exact h.elim (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => C8R02048_closed row h) (fun h => C8R02080_closed row h)) (fun h => h.elim (fun h => C8R02112_closed row h) (fun h => h.elim (fun h => C8R02144_closed row h) (fun h => C8R02176_closed row h)))) (fun h => h.elim (fun h => h.elim (fun h => C8R02208_closed row h) (fun h => h.elim (fun h => C8R02240_closed row h) (fun h => C8R02272_closed row h))) (fun h => h.elim (fun h => C8R02304_closed row h) (fun h => h.elim (fun h => C8R02336_closed row h) (fun h => C8R02368_closed row h))))) (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => C8R02400_closed row h) (fun h => C8R02432_closed row h)) (fun h => h.elim (fun h => C8R02464_closed row h) (fun h => h.elim (fun h => C8R02496_closed row h) (fun h => C8R02528_closed row h)))) (fun h => h.elim (fun h => h.elim (fun h => C8R02560_closed row h) (fun h => h.elim (fun h => C8R02592_closed row h) (fun h => C8R02624_closed row h))) (fun h => h.elim (fun h => C8R02656_closed row h) (fun h => h.elim (fun h => C8R02688_closed row h) (fun h => C8R02720_closed row h)))))
end Polyomino57
