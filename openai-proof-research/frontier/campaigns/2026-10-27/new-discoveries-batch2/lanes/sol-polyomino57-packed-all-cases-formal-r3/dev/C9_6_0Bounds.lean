import C9_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 512, boundCheck 35 (table m.val) = true := by decide
end C9_6_0
