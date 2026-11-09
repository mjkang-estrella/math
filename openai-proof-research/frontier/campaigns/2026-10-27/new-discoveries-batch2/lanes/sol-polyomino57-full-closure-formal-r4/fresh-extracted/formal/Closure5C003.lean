import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_24 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3)]
def row5_24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(99,(1,0))),((0,-1),(51,(0,1))),((0,1),(38,(0,0))),((0,2),(70,(0,0))),((0,3),(74,(0,0))),((1,-1),(133,(0,1))),((1,4),(75,(0,0))),((2,0),(76,(0,0))),((2,1),(77,(0,0))),((2,2),(78,(0,0))),((2,3),(79,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_24_checked : successorFastRowCheck layer6 row5_24 row5_24choice = true := by decide
def row5_25 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0)]
def row5_25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(100,(1,0))),((0,-1),(52,(0,1))),((0,1),(39,(0,0))),((0,2),(71,(0,0))),((1,-1),(135,(0,1))),((1,3),(76,(0,0))),((2,-1),(156,(0,1))),((2,1),(80,(0,0))),((2,2),(81,(0,0))),((3,0),(82,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_25_checked : successorFastRowCheck layer6 row5_25 row5_25choice = true := by decide
def row5_26 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1)]
def row5_26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(101,(1,0))),((0,-1),(53,(0,1))),((0,1),(40,(0,0))),((0,2),(72,(0,0))),((1,-1),(136,(0,1))),((1,3),(77,(0,0))),((2,0),(80,(0,0))),((2,2),(83,(0,0))),((3,1),(84,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_26_checked : successorFastRowCheck layer6 row5_26 row5_26choice = true := by decide
def row5_27 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2)]
def row5_27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(102,(1,0))),((0,-1),(54,(0,1))),((0,1),(41,(0,0))),((0,2),(73,(0,0))),((1,-1),(137,(0,1))),((1,3),(78,(0,0))),((2,0),(81,(0,0))),((2,1),(83,(0,0))),((2,3),(85,(0,0))),((3,2),(86,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_27_checked : successorFastRowCheck layer6 row5_27 row5_27choice = true := by decide
def row5_28 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1)]
def row5_28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(103,(1,0))),((0,-1),(56,(0,1))),((0,1),(42,(0,0))),((1,-1),(141,(0,1))),((1,2),(80,(0,0))),((2,-1),(157,(0,1))),((2,2),(87,(0,0))),((3,0),(88,(0,0))),((3,1),(89,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_28_checked : successorFastRowCheck layer6 row5_28 row5_28choice = true := by decide
def row5_29 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0)]
def row5_29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(104,(1,0))),((0,-1),(57,(0,1))),((0,1),(43,(0,0))),((1,-1),(142,(0,1))),((1,2),(82,(0,0))),((2,-1),(159,(0,1))),((2,1),(88,(0,0))),((3,-1),(160,(0,1))),((3,1),(90,(0,0))),((4,0),(91,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_29_checked : successorFastRowCheck layer6 row5_29 row5_29choice = true := by decide
def row5_30 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2)]
def row5_30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(105,(1,0))),((0,-1),(58,(0,1))),((0,1),(44,(0,0))),((1,-1),(143,(0,1))),((1,2),(83,(0,0))),((2,0),(87,(0,0))),((2,3),(92,(0,0))),((3,1),(93,(0,0))),((3,2),(94,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_30_checked : successorFastRowCheck layer6 row5_30 row5_30choice = true := by decide
def row5_31 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1)]
def row5_31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(106,(1,0))),((0,-1),(59,(0,1))),((0,1),(45,(0,0))),((1,-1),(144,(0,1))),((1,2),(84,(0,0))),((2,0),(89,(0,0))),((2,2),(93,(0,0))),((3,0),(95,(0,0))),((3,2),(96,(0,0))),((4,1),(97,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_31_checked : successorFastRowCheck layer6 row5_31 row5_31choice = true := by decide
def Closure5C003rows : List (List GridPoint) := [row5_24,row5_25,row5_26,row5_27,row5_28,row5_29,row5_30,row5_31]
theorem Closure5C003_closed : ∀ row ∈ Closure5C003rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C003rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_24choice,row5_24_checked⟩
  · subst row
    exact ⟨row5_25choice,row5_25_checked⟩
  · subst row
    exact ⟨row5_26choice,row5_26_checked⟩
  · subst row
    exact ⟨row5_27choice,row5_27_checked⟩
  · subst row
    exact ⟨row5_28choice,row5_28_checked⟩
  · subst row
    exact ⟨row5_29choice,row5_29_checked⟩
  · subst row
    exact ⟨row5_30choice,row5_30_checked⟩
  · subst row
    exact ⟨row5_31choice,row5_31_checked⟩
end Polyomino57
