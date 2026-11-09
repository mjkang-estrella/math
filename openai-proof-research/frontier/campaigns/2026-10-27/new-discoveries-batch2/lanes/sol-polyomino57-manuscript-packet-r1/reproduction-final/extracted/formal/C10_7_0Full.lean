import C10_7_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem full_check : ∀ v : Fin 44, 12 ≤ value (Finset.range 6) v := by decide
end C10_7_0
