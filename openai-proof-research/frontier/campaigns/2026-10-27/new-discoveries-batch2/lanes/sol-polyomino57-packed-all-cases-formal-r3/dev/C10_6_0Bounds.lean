import C10_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 128, boundCheck 39 (table m.val) = true := by decide
end C10_6_0
