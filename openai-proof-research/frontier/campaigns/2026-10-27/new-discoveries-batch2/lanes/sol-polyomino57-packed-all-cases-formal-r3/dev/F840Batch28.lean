import F840Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs28 : List (Finset GridPoint × Finset GridPoint) := [({(4,2),(5,1),(5,3)},{(1,0)}),({(4,2),(5,1),(6,2)},{(1,0)}),({(4,2),(5,3),(6,2)},{(1,0)}),({(4,4),(5,1),(5,3)},{(1,0)}),({(4,4),(5,1),(6,2)},{(1,0)}),({(4,4),(5,3),(6,2)},{(1,0)}),({(5,1),(5,3),(6,2)},{(1,0)})]
theorem checked28 : ∀ es ∈ pairs28, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide
end F840
