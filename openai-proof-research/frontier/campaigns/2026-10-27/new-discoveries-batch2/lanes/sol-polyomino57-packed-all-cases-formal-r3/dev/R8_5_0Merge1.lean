import R8_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check1 : ∀ u : Fin 4, halfCheck 9 27 table (u.val+4) = true := by decide
end R8_5_0
