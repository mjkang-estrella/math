import R9_5_0Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_checkB7 : ∀ m : Fin 32, (m.val+224) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+224)) vw.1.val ≤ digit (table (m.val+224)) vw.2.val + 1 := by decide
end R9_5_0
