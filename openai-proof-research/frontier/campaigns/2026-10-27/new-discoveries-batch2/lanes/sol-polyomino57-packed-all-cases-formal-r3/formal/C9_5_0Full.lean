import C9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem full_check : ∀ v : Fin 30, 12 ≤ value (Finset.range 10) v := by decide
end C9_5_0
