import R6_6_1Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check139 : ∀ m : Fin 8, (m.val+1112) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+1112)) vw.1.val ≤ digit (table (m.val+1112)) vw.2.val + 1 := by decide
end R6_6_1
