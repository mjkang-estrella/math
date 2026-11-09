import R8_4_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check83 : ∀ u : Fin 4, halfCheck 9 22 table (u.val+332) = true := by decide
end R8_4_1
