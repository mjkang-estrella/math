import F830Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F830
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs0 : List (Finset GridPoint × Finset GridPoint) := [({(0,0)},{(0,0),(1,0)}),({(1,-1)},{(1,-1),(1,0),(2,-1)}),({(1,1)},{(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)}),({(2,0)},{(1,0),(2,-1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)}),({(3,3)},{(1,0)}),({(4,2)},{(1,0)}),({(4,4)},{(1,0)}),({(5,3)},{(1,0)})]
theorem checked0 : ∀ es ∈ pairs0, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide
end F830
