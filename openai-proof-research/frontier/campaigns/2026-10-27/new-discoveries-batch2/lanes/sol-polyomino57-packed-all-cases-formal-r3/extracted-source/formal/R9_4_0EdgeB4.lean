import R9_4_0Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_4_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_checkB4 : ∀ m : Fin 32, (m.val+128) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+128)) vw.1.val ≤ digit (table (m.val+128)) vw.2.val + 1 := by decide
end R9_4_0
