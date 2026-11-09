import R8_4_1Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check47 : ∀ m : Fin 8, (m.val+376) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+376)) vw.1.val ≤ digit (table (m.val+376)) vw.2.val + 1 := by decide
end R8_4_1
