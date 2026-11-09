import F740Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F740
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
def pairs0 : List (Finset GridPoint × Finset GridPoint) := [({(0,0)},{(0,0),(1,-1),(1,0),(2,-1)}),({(1,1)},{(1,-1),(1,0),(1,1),(2,-1),(2,1)}),({(2,-2)},{(1,-1),(1,0),(2,-2),(2,-1)}),({(2,0)},{(1,-1),(1,0),(2,-1),(2,0),(2,1),(3,0)}),({(2,2)},{(1,-1),(1,0),(2,-1)}),({(3,-1)},{(1,-1),(1,0),(2,-1),(3,-1),(3,0)}),({(3,1)},{(1,-1),(1,0),(2,-1)}),({(3,3)},{(1,-1),(1,0),(2,-1)}),({(4,0)},{(1,-1),(1,0),(2,-1)}),({(5,1)},{(1,-1),(1,0),(2,-1)})]
theorem checked0 : ∀ es ∈ pairs0, CutGood (forced ∪ es.1) es.2 ∨ Disjoint (forced ∪ es.1) miss := by decide
end F740
