import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_32 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2)]
def row5_32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(107,(1,0))),((0,-1),(63,(0,1))),((0,1),(46,(0,0))),((1,-1),(150,(0,1))),((1,1),(87,(0,0))),((1,2),(98,(0,0))),((2,-1),(161,(0,1))),((2,3),(99,(0,0))),((3,0),(100,(0,0))),((3,1),(101,(0,0))),((3,2),(102,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_32_checked : successorFastRowCheck layer6 row5_32 row5_32choice = true := by decide
def row5_33 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0)]
def row5_33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(108,(1,0))),((0,-1),(64,(0,1))),((0,1),(47,(0,0))),((1,-1),(151,(0,1))),((1,1),(88,(0,0))),((2,-1),(163,(0,1))),((2,2),(100,(0,0))),((3,-1),(169,(0,1))),((3,1),(103,(0,0))),((4,0),(104,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_33_checked : successorFastRowCheck layer6 row5_33 row5_33choice = true := by decide
def row5_34 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1)]
def row5_34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(109,(1,0))),((0,-1),(65,(0,1))),((0,1),(48,(0,0))),((1,-1),(152,(0,1))),((1,1),(89,(0,0))),((2,-1),(164,(0,1))),((2,2),(101,(0,0))),((3,0),(103,(0,0))),((3,2),(105,(0,0))),((4,1),(106,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_34_checked : successorFastRowCheck layer6 row5_34 row5_34choice = true := by decide
def row5_35 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1)]
def row5_35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(110,(1,0))),((0,-1),(67,(0,1))),((0,1),(49,(0,0))),((1,-1),(154,(0,1))),((1,1),(90,(0,0))),((2,-1),(167,(0,1))),((2,1),(103,(0,0))),((3,-1),(170,(0,1))),((3,2),(107,(0,0))),((4,0),(108,(0,0))),((4,1),(109,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_35_checked : successorFastRowCheck layer6 row5_35 row5_35choice = true := by decide
def row5_36 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0)]
def row5_36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(111,(1,0))),((0,-1),(68,(0,1))),((0,1),(50,(0,0))),((1,-1),(155,(0,1))),((1,1),(91,(0,0))),((2,-1),(168,(0,1))),((2,1),(104,(0,0))),((3,-1),(172,(0,1))),((3,1),(108,(0,0))),((4,-1),(173,(0,1))),((4,1),(110,(0,0))),((5,0),(111,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_36_checked : successorFastRowCheck layer6 row5_36 row5_36choice = true := by decide
def row5_37 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1)]
def row5_37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(156,(1,0))),((-1,2),(194,(1,0))),((-1,3),(212,(1,0))),((0,0),(6,(0,0))),((0,4),(112,(0,0))),((1,-1),(174,(0,1))),((1,2),(113,(0,0))),((1,3),(114,(0,0))),((2,0),(115,(0,0))),((2,1),(116,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_37_checked : successorFastRowCheck layer6 row5_37 row5_37choice = true := by decide
def row5_38 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2)]
def row5_38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(157,(1,0))),((-1,2),(195,(1,0))),((0,0),(17,(0,0))),((0,3),(113,(0,0))),((1,-1),(175,(0,1))),((1,3),(118,(0,0))),((2,0),(119,(0,0))),((2,1),(120,(0,0))),((2,2),(121,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_38_checked : successorFastRowCheck layer6 row5_38 row5_38choice = true := by decide
def row5_39 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0)]
def row5_39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(158,(1,0))),((-1,2),(196,(1,0))),((0,0),(18,(0,0))),((0,3),(115,(0,0))),((1,-1),(177,(0,1))),((1,2),(119,(0,0))),((2,-1),(179,(0,1))),((2,1),(122,(0,0))),((3,0),(123,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_39_checked : successorFastRowCheck layer6 row5_39 row5_39choice = true := by decide
def Closure5C004rows : List (List GridPoint) := [row5_32,row5_33,row5_34,row5_35,row5_36,row5_37,row5_38,row5_39]
theorem Closure5C004_closed : ∀ row ∈ Closure5C004rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C004rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_32choice,row5_32_checked⟩
  · subst row
    exact ⟨row5_33choice,row5_33_checked⟩
  · subst row
    exact ⟨row5_34choice,row5_34_checked⟩
  · subst row
    exact ⟨row5_35choice,row5_35_checked⟩
  · subst row
    exact ⟨row5_36choice,row5_36_checked⟩
  · subst row
    exact ⟨row5_37choice,row5_37_checked⟩
  · subst row
    exact ⟨row5_38choice,row5_38_checked⟩
  · subst row
    exact ⟨row5_39choice,row5_39_checked⟩
end Polyomino57
