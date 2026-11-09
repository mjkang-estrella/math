import F840Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs21 : List (Finset GridPoint × Finset GridPoint) := [({(2,2),(3,-1),(3,3)},{(1,0)}),({(2,2),(3,-1),(4,0)},{(1,0)}),({(2,2),(3,-1),(4,2)},{(1,0)}),({(2,2),(3,-1),(4,4)},{(1,0)}),({(2,2),(3,-1),(5,1)},{(1,0)}),({(2,2),(3,-1),(5,3)},{(1,0)}),({(2,2),(3,-1),(6,2)},{(1,0)}),({(2,2),(3,1),(3,3)},{(1,0)}),({(2,2),(3,1),(4,0)},{(1,0)}),({(2,2),(3,1),(4,2)},{(1,0)}),({(2,2),(3,1),(4,4)},{(1,0)}),({(2,2),(3,1),(5,1)},{(1,0)}),({(2,2),(3,1),(5,3)},{(1,0)}),({(2,2),(3,1),(6,2)},{(1,0)}),({(2,2),(3,3),(4,0)},{(1,0)}),({(2,2),(3,3),(4,2)},{(1,0)})]
theorem checked21 : ∀ es ∈ pairs21, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide
end F840
