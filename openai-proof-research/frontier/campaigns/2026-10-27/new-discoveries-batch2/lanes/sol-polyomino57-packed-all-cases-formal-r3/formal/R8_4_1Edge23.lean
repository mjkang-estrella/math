import R8_4_1Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check23 : ∀ m : Fin 8, (m.val+184) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+184)) vw.1.val ≤ digit (table (m.val+184)) vw.2.val + 1 := by decide
end R8_4_1
