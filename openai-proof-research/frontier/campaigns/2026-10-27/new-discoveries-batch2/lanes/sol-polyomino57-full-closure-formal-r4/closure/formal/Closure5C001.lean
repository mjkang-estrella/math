import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_8 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2)]
def row5_8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(83,(1,0))),((-1,1),(141,(1,0))),((-1,2),(189,(1,0))),((0,-1),(13,(0,1))),((0,3),(10,(0,0))),((1,0),(17,(0,0))),((1,3),(25,(0,0))),((2,1),(26,(0,0))),((2,2),(27,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_8_checked : successorFastRowCheck layer6 row5_8 row5_8choice = true := by decide
def row5_9 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1)]
def row5_9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(84,(1,0))),((-1,1),(142,(1,0))),((-1,2),(190,(1,0))),((0,-1),(14,(0,1))),((0,3),(12,(0,0))),((1,0),(19,(0,0))),((1,2),(26,(0,0))),((2,0),(28,(0,0))),((2,2),(29,(0,0))),((3,1),(30,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_9_checked : successorFastRowCheck layer6 row5_9 row5_9choice = true := by decide
def row5_10 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3)]
def row5_10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(85,(1,0))),((-1,1),(143,(1,0))),((-1,2),(191,(1,0))),((0,-1),(15,(0,1))),((0,3),(13,(0,0))),((1,0),(20,(0,0))),((1,1),(25,(0,0))),((1,4),(31,(0,0))),((2,2),(32,(0,0))),((2,3),(33,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_10_checked : successorFastRowCheck layer6 row5_10 row5_10choice = true := by decide
def row5_11 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2)]
def row5_11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(86,(1,0))),((-1,1),(144,(1,0))),((-1,2),(192,(1,0))),((0,-1),(16,(0,1))),((0,3),(14,(0,0))),((1,0),(22,(0,0))),((1,1),(27,(0,0))),((1,3),(32,(0,0))),((2,1),(34,(0,0))),((2,3),(35,(0,0))),((3,2),(36,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_11_checked : successorFastRowCheck layer6 row5_11 row5_11choice = true := by decide
def row5_12 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2)]
def row5_12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(87,(1,0))),((-1,1),(145,(1,0))),((0,-1),(25,(0,1))),((0,2),(17,(0,0))),((1,-1),(118,(0,1))),((1,3),(38,(0,0))),((2,0),(39,(0,0))),((2,1),(40,(0,0))),((2,2),(41,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_12_checked : successorFastRowCheck layer6 row5_12 row5_12choice = true := by decide
def row5_13 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0)]
def row5_13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(88,(1,0))),((-1,1),(146,(1,0))),((0,-1),(26,(0,1))),((0,2),(18,(0,0))),((1,-1),(120,(0,1))),((1,2),(39,(0,0))),((2,-1),(126,(0,1))),((2,1),(42,(0,0))),((3,0),(43,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_13_checked : successorFastRowCheck layer6 row5_13 row5_13choice = true := by decide
def row5_14 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1)]
def row5_14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(89,(1,0))),((-1,1),(147,(1,0))),((0,-1),(27,(0,1))),((0,2),(19,(0,0))),((1,-1),(121,(0,1))),((1,2),(40,(0,0))),((2,0),(42,(0,0))),((2,2),(44,(0,0))),((3,1),(45,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_14_checked : successorFastRowCheck layer6 row5_14 row5_14choice = true := by decide
def row5_15 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1)]
def row5_15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(90,(1,0))),((-1,1),(148,(1,0))),((0,-1),(29,(0,1))),((0,2),(23,(0,0))),((1,-1),(124,(0,1))),((1,1),(42,(0,0))),((2,-1),(127,(0,1))),((2,2),(46,(0,0))),((3,0),(47,(0,0))),((3,1),(48,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_15_checked : successorFastRowCheck layer6 row5_15 row5_15choice = true := by decide
def Closure5C001rows : List (List GridPoint) := [row5_8,row5_9,row5_10,row5_11,row5_12,row5_13,row5_14,row5_15]
theorem Closure5C001_closed : ∀ row ∈ Closure5C001rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C001rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_8choice,row5_8_checked⟩
  · subst row
    exact ⟨row5_9choice,row5_9_checked⟩
  · subst row
    exact ⟨row5_10choice,row5_10_checked⟩
  · subst row
    exact ⟨row5_11choice,row5_11_checked⟩
  · subst row
    exact ⟨row5_12choice,row5_12_checked⟩
  · subst row
    exact ⟨row5_13choice,row5_13_checked⟩
  · subst row
    exact ⟨row5_14choice,row5_14_checked⟩
  · subst row
    exact ⟨row5_15choice,row5_15_checked⟩
end Polyomino57
