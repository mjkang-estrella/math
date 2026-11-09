import R9_4_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_4_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB29 : ∀ u : Fin 10, unionCheck 9 25 table (u.val+457) = true := by decide
end R9_4_0
