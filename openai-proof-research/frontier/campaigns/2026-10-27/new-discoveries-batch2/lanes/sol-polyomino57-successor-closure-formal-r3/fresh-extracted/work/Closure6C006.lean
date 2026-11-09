import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_48 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1)]
def row6_48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(289,(1,0))),((-1,1),(484,(1,0))),((0,-1),(94,(0,1))),((0,2),(77,(0,0))),((1,-1),(398,(0,1))),((1,1),(138,(0,0))),((2,-1),(411,(0,1))),((2,2),(150,(0,0))),((3,0),(152,(0,0))),((3,2),(154,(0,0))),((4,1),(155,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_48_checked : successorFastRowCheck layer7 row6_48 row6_48choice = true := by decide
def row6_49 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1)]
def row6_49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(290,(1,0))),((-1,1),(485,(1,0))),((0,-1),(96,(0,1))),((0,2),(78,(0,0))),((1,-1),(400,(0,1))),((1,1),(139,(0,0))),((2,-1),(414,(0,1))),((2,1),(152,(0,0))),((3,-1),(417,(0,1))),((3,2),(156,(0,0))),((4,0),(157,(0,0))),((4,1),(158,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_49_checked : successorFastRowCheck layer7 row6_49 row6_49choice = true := by decide
def row6_50 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0)]
def row6_50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(291,(1,0))),((-1,1),(486,(1,0))),((0,-1),(97,(0,1))),((0,2),(79,(0,0))),((1,-1),(401,(0,1))),((1,1),(140,(0,0))),((2,-1),(415,(0,1))),((2,1),(153,(0,0))),((3,-1),(419,(0,1))),((3,1),(157,(0,0))),((4,-1),(420,(0,1))),((4,1),(159,(0,0))),((5,0),(160,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_50_checked : successorFastRowCheck layer7 row6_50 row6_50choice = true := by decide
def row6_51 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4)]
def row6_51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(292,(1,0))),((-1,1),(487,(1,0))),((0,-1),(98,(0,1))),((0,2),(80,(0,0))),((0,3),(119,(0,0))),((0,4),(123,(0,0))),((1,0),(124,(0,0))),((1,5),(161,(0,0))),((2,1),(162,(0,0))),((2,2),(163,(0,0))),((2,3),(164,(0,0))),((2,4),(165,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_51_checked : successorFastRowCheck layer7 row6_51 row6_51choice = true := by decide
def row6_52 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1)]
def row6_52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(293,(1,0))),((-1,1),(488,(1,0))),((0,-1),(99,(0,1))),((0,2),(81,(0,0))),((0,3),(120,(0,0))),((1,0),(126,(0,0))),((1,4),(162,(0,0))),((2,0),(166,(0,0))),((2,2),(167,(0,0))),((2,3),(168,(0,0))),((3,1),(169,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_52_checked : successorFastRowCheck layer7 row6_52 row6_52choice = true := by decide
def row6_53 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2)]
def row6_53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(294,(1,0))),((-1,1),(489,(1,0))),((0,-1),(100,(0,1))),((0,2),(82,(0,0))),((0,3),(121,(0,0))),((1,0),(127,(0,0))),((1,4),(163,(0,0))),((2,1),(167,(0,0))),((2,3),(170,(0,0))),((3,2),(171,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_53_checked : successorFastRowCheck layer7 row6_53 row6_53choice = true := by decide
def row6_54 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3)]
def row6_54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(295,(1,0))),((-1,1),(490,(1,0))),((0,-1),(101,(0,1))),((0,2),(83,(0,0))),((0,3),(122,(0,0))),((1,0),(128,(0,0))),((1,4),(164,(0,0))),((2,1),(168,(0,0))),((2,2),(170,(0,0))),((2,4),(172,(0,0))),((3,3),(173,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_54_checked : successorFastRowCheck layer7 row6_54 row6_54choice = true := by decide
def row6_55 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1)]
def row6_55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(296,(1,0))),((-1,1),(491,(1,0))),((0,-1),(102,(0,1))),((0,2),(84,(0,0))),((1,0),(129,(0,0))),((1,3),(166,(0,0))),((2,-1),(421,(0,1))),((2,2),(174,(0,0))),((3,0),(175,(0,0))),((3,1),(176,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_55_checked : successorFastRowCheck layer7 row6_55 row6_55choice = true := by decide
def Closure6C006rows : List (List GridPoint) := [row6_48,row6_49,row6_50,row6_51,row6_52,row6_53,row6_54,row6_55]
theorem Closure6C006_closed : ∀ row ∈ Closure6C006rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C006rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_48choice,row6_48_checked⟩
  · subst row
    exact ⟨row6_49choice,row6_49_checked⟩
  · subst row
    exact ⟨row6_50choice,row6_50_checked⟩
  · subst row
    exact ⟨row6_51choice,row6_51_checked⟩
  · subst row
    exact ⟨row6_52choice,row6_52_checked⟩
  · subst row
    exact ⟨row6_53choice,row6_53_checked⟩
  · subst row
    exact ⟨row6_54choice,row6_54_checked⟩
  · subst row
    exact ⟨row6_55choice,row6_55_checked⟩
end Polyomino57
