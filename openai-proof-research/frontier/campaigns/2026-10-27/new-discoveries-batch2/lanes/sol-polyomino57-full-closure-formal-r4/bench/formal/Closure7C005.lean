import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_40 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3)]
def row7_40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(833,(1,0))),((-1,1),(1499,(1,0))),((-1,2),(2087,(1,0))),((-1,3),(2481,(1,0))),((0,-1),(65,(0,1))),((0,4),(53,(0,0))),((1,0),(89,(0,0))),((1,2),(122,(0,0))),((1,4),(130,(0,0))),((2,1),(134,(0,0))),((2,2),(136,(0,0))),((2,4),(137,(0,0))),((3,3),(138,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_40_checked : successorFastRowCheck layer8 row7_40 row7_40choice = true := by decide
def row7_41 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1)]
def row7_41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(834,(1,0))),((-1,1),(1500,(1,0))),((-1,2),(2088,(1,0))),((-1,3),(2482,(1,0))),((0,-1),(66,(0,1))),((0,4),(57,(0,0))),((1,0),(90,(0,0))),((1,2),(123,(0,0))),((1,3),(132,(0,0))),((2,-1),(1178,(0,1))),((2,2),(139,(0,0))),((3,0),(140,(0,0))),((3,1),(141,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_41_checked : successorFastRowCheck layer8 row7_41 row7_41choice = true := by decide
def row7_42 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2)]
def row7_42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(835,(1,0))),((-1,1),(1501,(1,0))),((-1,2),(2089,(1,0))),((-1,3),(2483,(1,0))),((0,-1),(67,(0,1))),((0,4),(58,(0,0))),((1,0),(92,(0,0))),((1,2),(124,(0,0))),((1,3),(133,(0,0))),((2,0),(139,(0,0))),((2,3),(142,(0,0))),((3,1),(143,(0,0))),((3,2),(144,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_42_checked : successorFastRowCheck layer8 row7_42 row7_42choice = true := by decide
def row7_43 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1)]
def row7_43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(836,(1,0))),((-1,1),(1502,(1,0))),((-1,2),(2090,(1,0))),((-1,3),(2484,(1,0))),((0,-1),(68,(0,1))),((0,4),(59,(0,0))),((1,0),(93,(0,0))),((1,2),(125,(0,0))),((1,3),(135,(0,0))),((2,0),(141,(0,0))),((2,2),(143,(0,0))),((3,0),(145,(0,0))),((3,2),(146,(0,0))),((4,1),(147,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_43_checked : successorFastRowCheck layer8 row7_43 row7_43choice = true := by decide
def row7_44 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4)]
def row7_44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(837,(1,0))),((-1,1),(1503,(1,0))),((-1,2),(2091,(1,0))),((-1,3),(2485,(1,0))),((0,-1),(69,(0,1))),((0,4),(60,(0,0))),((1,0),(94,(0,0))),((1,1),(119,(0,0))),((1,5),(148,(0,0))),((2,2),(149,(0,0))),((2,3),(150,(0,0))),((2,4),(151,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_44_checked : successorFastRowCheck layer8 row7_44 row7_44choice = true := by decide
def row7_45 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2)]
def row7_45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(838,(1,0))),((-1,1),(1504,(1,0))),((-1,2),(2092,(1,0))),((-1,3),(2486,(1,0))),((0,-1),(70,(0,1))),((0,4),(61,(0,0))),((1,0),(96,(0,0))),((1,1),(121,(0,0))),((1,4),(149,(0,0))),((2,1),(152,(0,0))),((2,3),(153,(0,0))),((3,2),(154,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_45_checked : successorFastRowCheck layer8 row7_45 row7_45choice = true := by decide
def row7_46 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def row7_46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(839,(1,0))),((-1,1),(1505,(1,0))),((-1,2),(2093,(1,0))),((-1,3),(2487,(1,0))),((0,-1),(71,(0,1))),((0,4),(62,(0,0))),((1,0),(97,(0,0))),((1,1),(122,(0,0))),((1,4),(150,(0,0))),((2,2),(153,(0,0))),((2,4),(155,(0,0))),((3,3),(156,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_46_checked : successorFastRowCheck layer8 row7_46 row7_46choice = true := by decide
def row7_47 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2)]
def row7_47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(840,(1,0))),((-1,1),(1506,(1,0))),((-1,2),(2094,(1,0))),((-1,3),(2488,(1,0))),((0,-1),(72,(0,1))),((0,4),(66,(0,0))),((1,0),(101,(0,0))),((1,1),(124,(0,0))),((1,3),(152,(0,0))),((2,0),(157,(0,0))),((2,3),(158,(0,0))),((3,1),(159,(0,0))),((3,2),(160,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_47_checked : successorFastRowCheck layer8 row7_47 row7_47choice = true := by decide
def Closure7C005rows : List (List GridPoint) := [row7_40,row7_41,row7_42,row7_43,row7_44,row7_45,row7_46,row7_47]
theorem Closure7C005_closed : ∀ row ∈ Closure7C005rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C005rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_40choice,row7_40_checked⟩
  · subst row
    exact ⟨row7_41choice,row7_41_checked⟩
  · subst row
    exact ⟨row7_42choice,row7_42_checked⟩
  · subst row
    exact ⟨row7_43choice,row7_43_checked⟩
  · subst row
    exact ⟨row7_44choice,row7_44_checked⟩
  · subst row
    exact ⟨row7_45choice,row7_45_checked⟩
  · subst row
    exact ⟨row7_46choice,row7_46_checked⟩
  · subst row
    exact ⟨row7_47choice,row7_47_checked⟩
end Polyomino57
