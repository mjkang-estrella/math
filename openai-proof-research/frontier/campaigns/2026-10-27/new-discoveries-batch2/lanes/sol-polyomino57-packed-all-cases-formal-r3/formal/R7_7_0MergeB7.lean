import R7_7_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB7 : ∀ u : Fin 17, unionCheck 8 32 table (u.val+189) = true := by decide
end R7_7_0
