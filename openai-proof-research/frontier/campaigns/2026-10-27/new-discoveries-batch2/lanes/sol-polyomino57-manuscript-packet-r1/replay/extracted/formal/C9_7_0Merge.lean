import C9_7_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 256, unionCheck 8 40 table u.val = true := by decide
end C9_7_0
