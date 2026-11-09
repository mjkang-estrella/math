import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_40 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1)]
def row6_40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(281,(1,0))),((-1,1),(476,(1,0))),((0,-1),(82,(0,1))),((0,2),(59,(0,0))),((1,-1),(382,(0,1))),((1,3),(126,(0,0))),((2,0),(129,(0,0))),((2,2),(132,(0,0))),((3,1),(133,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_40_checked : successorFastRowCheck layer7 row6_40 row6_40choice = true := by decide
def row6_41 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2)]
def row6_41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(282,(1,0))),((-1,1),(477,(1,0))),((0,-1),(83,(0,1))),((0,2),(60,(0,0))),((1,-1),(383,(0,1))),((1,3),(127,(0,0))),((2,0),(130,(0,0))),((2,1),(132,(0,0))),((2,3),(134,(0,0))),((3,2),(135,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_41_checked : successorFastRowCheck layer7 row6_41 row6_41choice = true := by decide
def row6_42 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]
def row6_42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(283,(1,0))),((-1,1),(478,(1,0))),((0,-1),(85,(0,1))),((0,2),(61,(0,0))),((1,-1),(387,(0,1))),((1,2),(129,(0,0))),((2,-1),(404,(0,1))),((2,2),(136,(0,0))),((3,0),(137,(0,0))),((3,1),(138,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_42_checked : successorFastRowCheck layer7 row6_42 row6_42choice = true := by decide
def row6_43 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0)]
def row6_43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(284,(1,0))),((-1,1),(479,(1,0))),((0,-1),(86,(0,1))),((0,2),(62,(0,0))),((1,-1),(388,(0,1))),((1,2),(131,(0,0))),((2,-1),(406,(0,1))),((2,1),(137,(0,0))),((3,-1),(407,(0,1))),((3,1),(139,(0,0))),((4,0),(140,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_43_checked : successorFastRowCheck layer7 row6_43 row6_43choice = true := by decide
def row6_44 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2)]
def row6_44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(285,(1,0))),((-1,1),(480,(1,0))),((0,-1),(87,(0,1))),((0,2),(63,(0,0))),((1,-1),(389,(0,1))),((1,2),(132,(0,0))),((2,0),(136,(0,0))),((2,3),(141,(0,0))),((3,1),(142,(0,0))),((3,2),(143,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_44_checked : successorFastRowCheck layer7 row6_44 row6_44choice = true := by decide
def row6_45 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1)]
def row6_45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(286,(1,0))),((-1,1),(481,(1,0))),((0,-1),(88,(0,1))),((0,2),(64,(0,0))),((1,-1),(390,(0,1))),((1,2),(133,(0,0))),((2,0),(138,(0,0))),((2,2),(142,(0,0))),((3,0),(144,(0,0))),((3,2),(145,(0,0))),((4,1),(146,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_45_checked : successorFastRowCheck layer7 row6_45 row6_45choice = true := by decide
def row6_46 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2)]
def row6_46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(287,(1,0))),((-1,1),(482,(1,0))),((0,-1),(92,(0,1))),((0,2),(75,(0,0))),((1,-1),(396,(0,1))),((1,1),(136,(0,0))),((1,2),(147,(0,0))),((2,-1),(408,(0,1))),((2,3),(148,(0,0))),((3,0),(149,(0,0))),((3,1),(150,(0,0))),((3,2),(151,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_46_checked : successorFastRowCheck layer7 row6_46 row6_46choice = true := by decide
def row6_47 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0)]
def row6_47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(288,(1,0))),((-1,1),(483,(1,0))),((0,-1),(93,(0,1))),((0,2),(76,(0,0))),((1,-1),(397,(0,1))),((1,1),(137,(0,0))),((2,-1),(410,(0,1))),((2,2),(149,(0,0))),((3,-1),(416,(0,1))),((3,1),(152,(0,0))),((4,0),(153,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_47_checked : successorFastRowCheck layer7 row6_47 row6_47choice = true := by decide
def Closure6C005rows : List (List GridPoint) := [row6_40,row6_41,row6_42,row6_43,row6_44,row6_45,row6_46,row6_47]
theorem Closure6C005_closed : ∀ row ∈ Closure6C005rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C005rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_40choice,row6_40_checked⟩
  · subst row
    exact ⟨row6_41choice,row6_41_checked⟩
  · subst row
    exact ⟨row6_42choice,row6_42_checked⟩
  · subst row
    exact ⟨row6_43choice,row6_43_checked⟩
  · subst row
    exact ⟨row6_44choice,row6_44_checked⟩
  · subst row
    exact ⟨row6_45choice,row6_45_checked⟩
  · subst row
    exact ⟨row6_46choice,row6_46_checked⟩
  · subst row
    exact ⟨row6_47choice,row6_47_checked⟩
end Polyomino57
