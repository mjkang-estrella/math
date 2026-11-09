import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_24 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0)]
def row6_24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(265,(1,0))),((-1,1),(460,(1,0))),((-1,2),(626,(1,0))),((0,-1),(43,(0,1))),((0,3),(34,(0,0))),((1,-1),(371,(0,1))),((1,1),(62,(0,0))),((1,2),(71,(0,0))),((2,-1),(376,(0,1))),((2,1),(76,(0,0))),((3,-1),(377,(0,1))),((3,1),(78,(0,0))),((4,0),(79,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_24_checked : successorFastRowCheck layer7 row6_24 row6_24choice = true := by decide
def row6_25 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3)]
def row6_25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(266,(1,0))),((-1,1),(461,(1,0))),((-1,2),(627,(1,0))),((0,-1),(44,(0,1))),((0,3),(35,(0,0))),((1,0),(57,(0,0))),((1,4),(80,(0,0))),((2,1),(81,(0,0))),((2,2),(82,(0,0))),((2,3),(83,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_25_checked : successorFastRowCheck layer7 row6_25 row6_25choice = true := by decide
def row6_26 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1)]
def row6_26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(267,(1,0))),((-1,1),(462,(1,0))),((-1,2),(628,(1,0))),((0,-1),(45,(0,1))),((0,3),(36,(0,0))),((1,0),(59,(0,0))),((1,3),(81,(0,0))),((2,0),(84,(0,0))),((2,2),(85,(0,0))),((3,1),(86,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_26_checked : successorFastRowCheck layer7 row6_26 row6_26choice = true := by decide
def row6_27 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
def row6_27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(268,(1,0))),((-1,1),(463,(1,0))),((-1,2),(629,(1,0))),((0,-1),(46,(0,1))),((0,3),(37,(0,0))),((1,0),(60,(0,0))),((1,3),(82,(0,0))),((2,1),(85,(0,0))),((2,3),(87,(0,0))),((3,2),(88,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_27_checked : successorFastRowCheck layer7 row6_27 row6_27choice = true := by decide
def row6_28 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1)]
def row6_28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(269,(1,0))),((-1,1),(464,(1,0))),((-1,2),(630,(1,0))),((0,-1),(47,(0,1))),((0,3),(41,(0,0))),((1,0),(61,(0,0))),((1,2),(84,(0,0))),((2,-1),(378,(0,1))),((2,2),(89,(0,0))),((3,0),(90,(0,0))),((3,1),(91,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_28_checked : successorFastRowCheck layer7 row6_28 row6_28choice = true := by decide
def row6_29 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2)]
def row6_29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(270,(1,0))),((-1,1),(465,(1,0))),((-1,2),(631,(1,0))),((0,-1),(48,(0,1))),((0,3),(42,(0,0))),((1,0),(63,(0,0))),((1,2),(85,(0,0))),((2,0),(89,(0,0))),((2,3),(92,(0,0))),((3,1),(93,(0,0))),((3,2),(94,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_29_checked : successorFastRowCheck layer7 row6_29 row6_29choice = true := by decide
def row6_30 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1)]
def row6_30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(271,(1,0))),((-1,1),(466,(1,0))),((-1,2),(632,(1,0))),((0,-1),(49,(0,1))),((0,3),(43,(0,0))),((1,0),(64,(0,0))),((1,2),(86,(0,0))),((2,0),(91,(0,0))),((2,2),(93,(0,0))),((3,0),(95,(0,0))),((3,2),(96,(0,0))),((4,1),(97,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_30_checked : successorFastRowCheck layer7 row6_30 row6_30choice = true := by decide
def row6_31 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4)]
def row6_31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(272,(1,0))),((-1,1),(467,(1,0))),((-1,2),(633,(1,0))),((0,-1),(50,(0,1))),((0,3),(44,(0,0))),((0,4),(56,(0,0))),((1,0),(65,(0,0))),((1,1),(80,(0,0))),((1,5),(98,(0,0))),((2,2),(99,(0,0))),((2,3),(100,(0,0))),((2,4),(101,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_31_checked : successorFastRowCheck layer7 row6_31 row6_31choice = true := by decide
def Closure6C003rows : List (List GridPoint) := [row6_24,row6_25,row6_26,row6_27,row6_28,row6_29,row6_30,row6_31]
theorem Closure6C003_closed : ∀ row ∈ Closure6C003rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C003rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_24choice,row6_24_checked⟩
  · subst row
    exact ⟨row6_25choice,row6_25_checked⟩
  · subst row
    exact ⟨row6_26choice,row6_26_checked⟩
  · subst row
    exact ⟨row6_27choice,row6_27_checked⟩
  · subst row
    exact ⟨row6_28choice,row6_28_checked⟩
  · subst row
    exact ⟨row6_29choice,row6_29_checked⟩
  · subst row
    exact ⟨row6_30choice,row6_30_checked⟩
  · subst row
    exact ⟨row6_31choice,row6_31_checked⟩
end Polyomino57
