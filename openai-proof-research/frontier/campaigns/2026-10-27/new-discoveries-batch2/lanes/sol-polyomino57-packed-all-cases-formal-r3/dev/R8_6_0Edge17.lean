import R8_6_0Edges
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check17 : ∀ m : Fin 8, (m.val+136) ≠ 0 → ∀ vw ∈ edges,
  digit (table (m.val+136)) vw.1.val ≤ digit (table (m.val+136)) vw.2.val + 1 := by decide
end R8_6_0
