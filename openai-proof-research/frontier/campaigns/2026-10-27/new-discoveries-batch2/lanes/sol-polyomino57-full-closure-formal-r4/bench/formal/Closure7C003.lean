import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_24 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3)]
def row7_24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(817,(1,0))),((-1,1),(1483,(1,0))),((-1,2),(2071,(1,0))),((-1,3),(2465,(1,0))),((0,-1),(48,(0,1))),((0,4),(31,(0,0))),((1,-1),(1155,(0,1))),((1,2),(82,(0,0))),((1,4),(86,(0,0))),((2,0),(87,(0,0))),((2,1),(88,(0,0))),((2,3),(89,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_24_checked : successorFastRowCheck layer8 row7_24 row7_24choice = true := by decide
def row7_25 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)]
def row7_25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(818,(1,0))),((-1,1),(1484,(1,0))),((-1,2),(2072,(1,0))),((-1,3),(2466,(1,0))),((0,-1),(49,(0,1))),((0,4),(33,(0,0))),((1,-1),(1157,(0,1))),((1,2),(83,(0,0))),((1,3),(87,(0,0))),((2,-1),(1171,(0,1))),((2,1),(90,(0,0))),((3,0),(91,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_25_checked : successorFastRowCheck layer8 row7_25 row7_25choice = true := by decide
def row7_26 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1)]
def row7_26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(819,(1,0))),((-1,1),(1485,(1,0))),((-1,2),(2073,(1,0))),((-1,3),(2467,(1,0))),((0,-1),(50,(0,1))),((0,4),(34,(0,0))),((1,-1),(1158,(0,1))),((1,2),(84,(0,0))),((1,3),(88,(0,0))),((2,0),(90,(0,0))),((2,2),(92,(0,0))),((3,1),(93,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_26_checked : successorFastRowCheck layer8 row7_26 row7_26choice = true := by decide
def row7_27 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3)]
def row7_27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(820,(1,0))),((-1,1),(1486,(1,0))),((-1,2),(2074,(1,0))),((-1,3),(2468,(1,0))),((0,-1),(51,(0,1))),((0,4),(35,(0,0))),((1,-1),(1159,(0,1))),((1,1),(82,(0,0))),((1,4),(94,(0,0))),((2,0),(95,(0,0))),((2,2),(96,(0,0))),((2,3),(97,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_27_checked : successorFastRowCheck layer8 row7_27 row7_27choice = true := by decide
def row7_28 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0)]
def row7_28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(821,(1,0))),((-1,1),(1487,(1,0))),((-1,2),(2075,(1,0))),((-1,3),(2469,(1,0))),((0,-1),(52,(0,1))),((0,4),(37,(0,0))),((1,-1),(1161,(0,1))),((1,1),(83,(0,0))),((1,3),(95,(0,0))),((2,-1),(1172,(0,1))),((2,1),(98,(0,0))),((2,2),(99,(0,0))),((3,0),(100,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_28_checked : successorFastRowCheck layer8 row7_28 row7_28choice = true := by decide
def row7_29 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2)]
def row7_29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(822,(1,0))),((-1,1),(1488,(1,0))),((-1,2),(2076,(1,0))),((-1,3),(2470,(1,0))),((0,-1),(53,(0,1))),((0,4),(38,(0,0))),((1,-1),(1162,(0,1))),((1,1),(85,(0,0))),((1,3),(96,(0,0))),((2,0),(99,(0,0))),((2,1),(101,(0,0))),((2,3),(102,(0,0))),((3,2),(103,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_29_checked : successorFastRowCheck layer8 row7_29 row7_29choice = true := by decide
def row7_30 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4)]
def row7_30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(823,(1,0))),((-1,1),(1489,(1,0))),((-1,2),(2077,(1,0))),((-1,3),(2471,(1,0))),((0,-1),(54,(0,1))),((0,4),(39,(0,0))),((1,-1),(1163,(0,1))),((1,1),(86,(0,0))),((1,2),(94,(0,0))),((1,5),(104,(0,0))),((2,0),(105,(0,0))),((2,3),(106,(0,0))),((2,4),(107,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_30_checked : successorFastRowCheck layer8 row7_30 row7_30choice = true := by decide
def row7_31 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0)]
def row7_31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(824,(1,0))),((-1,1),(1490,(1,0))),((-1,2),(2078,(1,0))),((-1,3),(2472,(1,0))),((0,-1),(55,(0,1))),((0,4),(40,(0,0))),((1,-1),(1165,(0,1))),((1,1),(87,(0,0))),((1,2),(95,(0,0))),((1,4),(105,(0,0))),((2,-1),(1173,(0,1))),((2,1),(108,(0,0))),((2,3),(109,(0,0))),((3,0),(110,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_31_checked : successorFastRowCheck layer8 row7_31 row7_31choice = true := by decide
def Closure7C003rows : List (List GridPoint) := [row7_24,row7_25,row7_26,row7_27,row7_28,row7_29,row7_30,row7_31]
theorem Closure7C003_closed : ∀ row ∈ Closure7C003rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C003rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_24choice,row7_24_checked⟩
  · subst row
    exact ⟨row7_25choice,row7_25_checked⟩
  · subst row
    exact ⟨row7_26choice,row7_26_checked⟩
  · subst row
    exact ⟨row7_27choice,row7_27_checked⟩
  · subst row
    exact ⟨row7_28choice,row7_28_checked⟩
  · subst row
    exact ⟨row7_29choice,row7_29_checked⟩
  · subst row
    exact ⟨row7_30choice,row7_30_checked⟩
  · subst row
    exact ⟨row7_31choice,row7_31_checked⟩
end Polyomino57
