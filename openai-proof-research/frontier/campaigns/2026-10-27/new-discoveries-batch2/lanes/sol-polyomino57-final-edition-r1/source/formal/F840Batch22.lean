import F840Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs22 : List (Finset GridPoint × Finset GridPoint) := [({(2,2),(3,3),(4,4)},{(1,0)}),({(2,2),(3,3),(5,1)},{(1,0)}),({(2,2),(3,3),(5,3)},{(1,0)}),({(2,2),(3,3),(6,2)},{(1,0)}),({(2,2),(4,0),(4,2)},{(1,0)}),({(2,2),(4,0),(4,4)},{(1,0)}),({(2,2),(4,0),(5,1)},{(1,0)}),({(2,2),(4,0),(5,3)},{(1,0)}),({(2,2),(4,0),(6,2)},{(1,0)}),({(2,2),(4,2),(4,4)},{(1,0)}),({(2,2),(4,2),(5,1)},{(1,0)}),({(2,2),(4,2),(5,3)},{(1,0)}),({(2,2),(4,2),(6,2)},{(1,0)}),({(2,2),(4,4),(5,1)},{(1,0)}),({(2,2),(4,4),(5,3)},{(1,0)}),({(2,2),(4,4),(6,2)},{(1,0)})]
theorem checked22 : ∀ es ∈ pairs22, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide
end F840
