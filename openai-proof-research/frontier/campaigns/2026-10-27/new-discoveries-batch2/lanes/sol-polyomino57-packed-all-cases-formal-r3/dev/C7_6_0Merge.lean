import C7_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C7_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 8192, unionCheck 13 28 table u.val = true := by decide
end C7_6_0
