import R8_4_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_checkB1 : ∀ m : Fin 256, boundCheck 22 (table (m.val+256)) = true := by decide
end R8_4_1
