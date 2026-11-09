import C8_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C8_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 8192, boundCheck 27 (table m.val) = true := by decide
end C8_5_0
