import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_32 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2)]
def row6_32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(273,(1,0))),((-1,1),(468,(1,0))),((-1,2),(634,(1,0))),((0,-1),(51,(0,1))),((0,3),(45,(0,0))),((1,0),(67,(0,0))),((1,1),(82,(0,0))),((1,4),(99,(0,0))),((2,1),(102,(0,0))),((2,3),(103,(0,0))),((3,2),(104,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_32_checked : successorFastRowCheck layer7 row6_32 row6_32choice = true := by decide
def row6_33 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3)]
def row6_33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(274,(1,0))),((-1,1),(469,(1,0))),((-1,2),(635,(1,0))),((0,-1),(52,(0,1))),((0,3),(46,(0,0))),((1,0),(68,(0,0))),((1,1),(83,(0,0))),((1,4),(100,(0,0))),((2,2),(103,(0,0))),((2,4),(105,(0,0))),((3,3),(106,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_33_checked : successorFastRowCheck layer7 row6_33 row6_33choice = true := by decide
def row6_34 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2)]
def row6_34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(275,(1,0))),((-1,1),(470,(1,0))),((-1,2),(636,(1,0))),((0,-1),(53,(0,1))),((0,3),(47,(0,0))),((1,0),(72,(0,0))),((1,1),(85,(0,0))),((1,3),(102,(0,0))),((2,0),(107,(0,0))),((2,3),(108,(0,0))),((3,1),(109,(0,0))),((3,2),(110,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_34_checked : successorFastRowCheck layer7 row6_34 row6_34choice = true := by decide
def row6_35 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3)]
def row6_35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(276,(1,0))),((-1,1),(471,(1,0))),((-1,2),(637,(1,0))),((0,-1),(54,(0,1))),((0,3),(48,(0,0))),((1,0),(73,(0,0))),((1,1),(87,(0,0))),((1,3),(103,(0,0))),((2,1),(108,(0,0))),((2,4),(111,(0,0))),((3,2),(112,(0,0))),((3,3),(113,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_35_checked : successorFastRowCheck layer7 row6_35 row6_35choice = true := by decide
def row6_36 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2)]
def row6_36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(277,(1,0))),((-1,1),(472,(1,0))),((-1,2),(638,(1,0))),((0,-1),(55,(0,1))),((0,3),(49,(0,0))),((1,0),(74,(0,0))),((1,1),(88,(0,0))),((1,3),(104,(0,0))),((2,1),(110,(0,0))),((2,3),(112,(0,0))),((3,1),(114,(0,0))),((3,3),(115,(0,0))),((4,2),(116,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_36_checked : successorFastRowCheck layer7 row6_36 row6_36choice = true := by decide
def row6_37 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3)]
def row6_37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(278,(1,0))),((-1,1),(473,(1,0))),((-1,3),(722,(1,0))),((0,-1),(56,(0,1))),((0,2),(35,(0,0))),((0,4),(117,(0,0))),((1,0),(118,(0,0))),((1,4),(119,(0,0))),((2,1),(120,(0,0))),((2,2),(121,(0,0))),((2,3),(122,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_37_checked : successorFastRowCheck layer7 row6_37 row6_37choice = true := by decide
def row6_38 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3)]
def row6_38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(279,(1,0))),((-1,1),(474,(1,0))),((0,-1),(80,(0,1))),((0,2),(57,(0,0))),((0,3),(118,(0,0))),((1,-1),(379,(0,1))),((1,4),(124,(0,0))),((2,0),(125,(0,0))),((2,1),(126,(0,0))),((2,2),(127,(0,0))),((2,3),(128,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_38_checked : successorFastRowCheck layer7 row6_38 row6_38choice = true := by decide
def row6_39 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0)]
def row6_39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(280,(1,0))),((-1,1),(475,(1,0))),((0,-1),(81,(0,1))),((0,2),(58,(0,0))),((1,-1),(381,(0,1))),((1,3),(125,(0,0))),((2,-1),(403,(0,1))),((2,1),(129,(0,0))),((2,2),(130,(0,0))),((3,0),(131,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_39_checked : successorFastRowCheck layer7 row6_39 row6_39choice = true := by decide
def Closure6C004rows : List (List GridPoint) := [row6_32,row6_33,row6_34,row6_35,row6_36,row6_37,row6_38,row6_39]
theorem Closure6C004_closed : ∀ row ∈ Closure6C004rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C004rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_32choice,row6_32_checked⟩
  · subst row
    exact ⟨row6_33choice,row6_33_checked⟩
  · subst row
    exact ⟨row6_34choice,row6_34_checked⟩
  · subst row
    exact ⟨row6_35choice,row6_35_checked⟩
  · subst row
    exact ⟨row6_36choice,row6_36_checked⟩
  · subst row
    exact ⟨row6_37choice,row6_37_checked⟩
  · subst row
    exact ⟨row6_38choice,row6_38_checked⟩
  · subst row
    exact ⟨row6_39choice,row6_39_checked⟩
end Polyomino57
