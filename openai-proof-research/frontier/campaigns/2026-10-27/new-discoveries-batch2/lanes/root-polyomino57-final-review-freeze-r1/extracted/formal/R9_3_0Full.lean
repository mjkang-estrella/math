import R9_3_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem full_check : ∀ v : Fin 20, 12 ≤ value (Finset.range 6) v := by decide
end R9_3_0
