import C8_4_1Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 16384, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by decide
end C8_4_1
