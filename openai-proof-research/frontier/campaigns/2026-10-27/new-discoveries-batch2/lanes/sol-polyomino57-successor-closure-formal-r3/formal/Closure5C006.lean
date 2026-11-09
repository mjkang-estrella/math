import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_48 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2)]
def row5_48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(167,(1,0))),((0,0),(44,(0,0))),((0,2),(124,(0,0))),((1,-1),(191,(0,1))),((1,2),(141,(0,0))),((2,0),(145,(0,0))),((2,3),(150,(0,0))),((3,1),(151,(0,0))),((3,2),(152,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_48_checked : successorFastRowCheck layer6 row5_48 row5_48choice = true := by decide
def row5_49 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1)]
def row5_49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(168,(1,0))),((0,0),(45,(0,0))),((0,2),(125,(0,0))),((1,-1),(192,(0,1))),((1,2),(142,(0,0))),((2,0),(147,(0,0))),((2,2),(151,(0,0))),((3,0),(153,(0,0))),((3,2),(154,(0,0))),((4,1),(155,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_49_checked : successorFastRowCheck layer6 row5_49 row5_49choice = true := by decide
def row5_50 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1)]
def row5_50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(169,(1,0))),((0,0),(55,(0,0))),((0,2),(126,(0,0))),((1,0),(138,(0,0))),((1,3),(156,(0,0))),((2,-1),(199,(0,1))),((2,2),(157,(0,0))),((3,0),(158,(0,0))),((3,1),(159,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_50_checked : successorFastRowCheck layer6 row5_50 row5_50choice = true := by decide
def row5_51 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2)]
def row5_51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(170,(1,0))),((0,0),(60,(0,0))),((0,2),(127,(0,0))),((1,0),(145,(0,0))),((1,2),(157,(0,0))),((2,-1),(200,(0,1))),((2,3),(161,(0,0))),((3,0),(162,(0,0))),((3,1),(163,(0,0))),((3,2),(164,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_51_checked : successorFastRowCheck layer6 row5_51 row5_51choice = true := by decide
def row5_52 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0)]
def row5_52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(171,(1,0))),((0,0),(61,(0,0))),((0,2),(128,(0,0))),((1,0),(146,(0,0))),((1,2),(158,(0,0))),((2,-1),(202,(0,1))),((2,2),(162,(0,0))),((3,-1),(204,(0,1))),((3,1),(165,(0,0))),((4,0),(166,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_52_checked : successorFastRowCheck layer6 row5_52 row5_52choice = true := by decide
def row5_53 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1)]
def row5_53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(172,(1,0))),((0,0),(62,(0,0))),((0,2),(129,(0,0))),((1,0),(147,(0,0))),((1,2),(159,(0,0))),((2,-1),(203,(0,1))),((2,2),(163,(0,0))),((3,0),(165,(0,0))),((3,2),(167,(0,0))),((4,1),(168,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_53_checked : successorFastRowCheck layer6 row5_53 row5_53choice = true := by decide
def row5_54 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1)]
def row5_54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(173,(1,0))),((0,0),(66,(0,0))),((0,2),(130,(0,0))),((1,0),(153,(0,0))),((1,2),(160,(0,0))),((2,0),(165,(0,0))),((2,2),(169,(0,0))),((3,-1),(205,(0,1))),((3,2),(170,(0,0))),((4,0),(171,(0,0))),((4,1),(172,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_54_checked : successorFastRowCheck layer6 row5_54 row5_54choice = true := by decide
def row5_55 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2)]
def row5_55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(199,(1,0))),((-1,3),(213,(1,0))),((0,0),(69,(0,0))),((0,1),(113,(0,0))),((0,4),(174,(0,0))),((1,-1),(206,(0,1))),((1,3),(175,(0,0))),((2,0),(176,(0,0))),((2,1),(177,(0,0))),((2,2),(178,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_55_checked : successorFastRowCheck layer6 row5_55 row5_55choice = true := by decide
def Closure5C006rows : List (List GridPoint) := [row5_48,row5_49,row5_50,row5_51,row5_52,row5_53,row5_54,row5_55]
theorem Closure5C006_closed : ∀ row ∈ Closure5C006rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C006rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_48choice,row5_48_checked⟩
  · subst row
    exact ⟨row5_49choice,row5_49_checked⟩
  · subst row
    exact ⟨row5_50choice,row5_50_checked⟩
  · subst row
    exact ⟨row5_51choice,row5_51_checked⟩
  · subst row
    exact ⟨row5_52choice,row5_52_checked⟩
  · subst row
    exact ⟨row5_53choice,row5_53_checked⟩
  · subst row
    exact ⟨row5_54choice,row5_54_checked⟩
  · subst row
    exact ⟨row5_55choice,row5_55_checked⟩
end Polyomino57
