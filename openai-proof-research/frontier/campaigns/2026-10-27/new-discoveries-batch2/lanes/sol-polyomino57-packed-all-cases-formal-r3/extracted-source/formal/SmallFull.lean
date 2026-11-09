import SmallData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
theorem full_check : ∀ z : Fin 60, z ∈ Finset.univ → 12 ≤ value Finset.univ z := by decide
end Polyomino57.Diagonal.FiniteProof.Small
