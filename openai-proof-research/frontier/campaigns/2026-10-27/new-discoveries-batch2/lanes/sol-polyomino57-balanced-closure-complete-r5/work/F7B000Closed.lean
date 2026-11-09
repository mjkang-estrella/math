import C7R00000
import C7R00032
import C7R00064
import C7R00096
import C7R00128
import C7R00160
import C7R00192
import C7R00224
import C7R00256
import C7R00288
import C7R00320
import C7R00352
import C7R00384
import C7R00416
import C7R00448
import C7R00480
import C7R00512
import C7R00544
import C7R00576
import C7R00608
import C7R00640
import C7R00672
import C7R00704
import C7R00736
set_option autoImplicit false
namespace Polyomino57
theorem F7B000Closed (row : List GridPoint) (h : FamilyMember row F7B000) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  exact h.elim (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => C7R00000_closed row h) (fun h => h.elim (fun h => C7R00032_closed row h) (fun h => C7R00064_closed row h))) (fun h => h.elim (fun h => C7R00096_closed row h) (fun h => h.elim (fun h => C7R00128_closed row h) (fun h => C7R00160_closed row h)))) (fun h => h.elim (fun h => h.elim (fun h => C7R00192_closed row h) (fun h => h.elim (fun h => C7R00224_closed row h) (fun h => C7R00256_closed row h))) (fun h => h.elim (fun h => C7R00288_closed row h) (fun h => h.elim (fun h => C7R00320_closed row h) (fun h => C7R00352_closed row h))))) (fun h => h.elim (fun h => h.elim (fun h => h.elim (fun h => C7R00384_closed row h) (fun h => h.elim (fun h => C7R00416_closed row h) (fun h => C7R00448_closed row h))) (fun h => h.elim (fun h => C7R00480_closed row h) (fun h => h.elim (fun h => C7R00512_closed row h) (fun h => C7R00544_closed row h)))) (fun h => h.elim (fun h => h.elim (fun h => C7R00576_closed row h) (fun h => h.elim (fun h => C7R00608_closed row h) (fun h => C7R00640_closed row h))) (fun h => h.elim (fun h => C7R00672_closed row h) (fun h => h.elim (fun h => C7R00704_closed row h) (fun h => C7R00736_closed row h)))))
end Polyomino57
