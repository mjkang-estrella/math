import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_40 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1)]
def row5_40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(159,(1,0))),((-1,2),(197,(1,0))),((0,0),(19,(0,0))),((0,3),(116,(0,0))),((1,-1),(178,(0,1))),((1,2),(120,(0,0))),((2,0),(122,(0,0))),((2,2),(124,(0,0))),((3,1),(125,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_40_checked : successorFastRowCheck layer6 row5_40 row5_40choice = true := by decide
def row5_41 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1)]
def row5_41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(160,(1,0))),((-1,2),(198,(1,0))),((0,0),(28,(0,0))),((0,3),(117,(0,0))),((1,0),(122,(0,0))),((1,2),(126,(0,0))),((2,-1),(180,(0,1))),((2,2),(127,(0,0))),((3,0),(128,(0,0))),((3,1),(129,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_41_checked : successorFastRowCheck layer6 row5_41 row5_41choice = true := by decide
def row5_42 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3)]
def row5_42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(161,(1,0))),((0,0),(38,(0,0))),((0,2),(118,(0,0))),((0,3),(132,(0,0))),((1,-1),(181,(0,1))),((1,4),(133,(0,0))),((2,0),(134,(0,0))),((2,1),(135,(0,0))),((2,2),(136,(0,0))),((2,3),(137,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_42_checked : successorFastRowCheck layer6 row5_42 row5_42choice = true := by decide
def row5_43 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0)]
def row5_43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(162,(1,0))),((0,0),(39,(0,0))),((0,2),(119,(0,0))),((1,-1),(183,(0,1))),((1,3),(134,(0,0))),((2,-1),(194,(0,1))),((2,1),(138,(0,0))),((2,2),(139,(0,0))),((3,0),(140,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_43_checked : successorFastRowCheck layer6 row5_43 row5_43choice = true := by decide
def row5_44 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1)]
def row5_44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(163,(1,0))),((0,0),(40,(0,0))),((0,2),(120,(0,0))),((1,-1),(184,(0,1))),((1,3),(135,(0,0))),((2,0),(138,(0,0))),((2,2),(141,(0,0))),((3,1),(142,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_44_checked : successorFastRowCheck layer6 row5_44 row5_44choice = true := by decide
def row5_45 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2)]
def row5_45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(164,(1,0))),((0,0),(41,(0,0))),((0,2),(121,(0,0))),((1,-1),(185,(0,1))),((1,3),(136,(0,0))),((2,0),(139,(0,0))),((2,1),(141,(0,0))),((2,3),(143,(0,0))),((3,2),(144,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_45_checked : successorFastRowCheck layer6 row5_45 row5_45choice = true := by decide
def row5_46 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1)]
def row5_46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(165,(1,0))),((0,0),(42,(0,0))),((0,2),(122,(0,0))),((1,-1),(189,(0,1))),((1,2),(138,(0,0))),((2,-1),(195,(0,1))),((2,2),(145,(0,0))),((3,0),(146,(0,0))),((3,1),(147,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_46_checked : successorFastRowCheck layer6 row5_46 row5_46choice = true := by decide
def row5_47 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0)]
def row5_47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(166,(1,0))),((0,0),(43,(0,0))),((0,2),(123,(0,0))),((1,-1),(190,(0,1))),((1,2),(140,(0,0))),((2,-1),(197,(0,1))),((2,1),(146,(0,0))),((3,-1),(198,(0,1))),((3,1),(148,(0,0))),((4,0),(149,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_47_checked : successorFastRowCheck layer6 row5_47 row5_47choice = true := by decide
def Closure5C005rows : List (List GridPoint) := [row5_40,row5_41,row5_42,row5_43,row5_44,row5_45,row5_46,row5_47]
theorem Closure5C005_closed : ∀ row ∈ Closure5C005rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C005rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_40choice,row5_40_checked⟩
  · subst row
    exact ⟨row5_41choice,row5_41_checked⟩
  · subst row
    exact ⟨row5_42choice,row5_42_checked⟩
  · subst row
    exact ⟨row5_43choice,row5_43_checked⟩
  · subst row
    exact ⟨row5_44choice,row5_44_checked⟩
  · subst row
    exact ⟨row5_45choice,row5_45_checked⟩
  · subst row
    exact ⟨row5_46choice,row5_46_checked⟩
  · subst row
    exact ⟨row5_47choice,row5_47_checked⟩
end Polyomino57
