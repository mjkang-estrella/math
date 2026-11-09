import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_16 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0)]
def row5_16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(91,(1,0))),((-1,1),(149,(1,0))),((0,-1),(30,(0,1))),((0,2),(24,(0,0))),((1,-1),(125,(0,1))),((1,1),(43,(0,0))),((2,-1),(129,(0,1))),((2,1),(47,(0,0))),((3,-1),(130,(0,1))),((3,1),(49,(0,0))),((4,0),(50,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_16_checked : successorFastRowCheck layer6 row5_16 row5_16choice = true := by decide
def row5_17 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3)]
def row5_17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(92,(1,0))),((-1,1),(150,(1,0))),((0,-1),(31,(0,1))),((0,2),(25,(0,0))),((0,3),(37,(0,0))),((1,0),(38,(0,0))),((1,4),(51,(0,0))),((2,1),(52,(0,0))),((2,2),(53,(0,0))),((2,3),(54,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_17_checked : successorFastRowCheck layer6 row5_17 row5_17choice = true := by decide
def row5_18 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1)]
def row5_18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(93,(1,0))),((-1,1),(151,(1,0))),((0,-1),(32,(0,1))),((0,2),(26,(0,0))),((1,0),(40,(0,0))),((1,3),(52,(0,0))),((2,0),(55,(0,0))),((2,2),(56,(0,0))),((3,1),(57,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_18_checked : successorFastRowCheck layer6 row5_18 row5_18choice = true := by decide
def row5_19 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2)]
def row5_19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(94,(1,0))),((-1,1),(152,(1,0))),((0,-1),(33,(0,1))),((0,2),(27,(0,0))),((1,0),(41,(0,0))),((1,3),(53,(0,0))),((2,1),(56,(0,0))),((2,3),(58,(0,0))),((3,2),(59,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_19_checked : successorFastRowCheck layer6 row5_19 row5_19choice = true := by decide
def row5_20 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1)]
def row5_20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(95,(1,0))),((-1,1),(153,(1,0))),((0,-1),(34,(0,1))),((0,2),(28,(0,0))),((1,0),(42,(0,0))),((1,2),(55,(0,0))),((2,-1),(131,(0,1))),((2,2),(60,(0,0))),((3,0),(61,(0,0))),((3,1),(62,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_20_checked : successorFastRowCheck layer6 row5_20 row5_20choice = true := by decide
def row5_21 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2)]
def row5_21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(96,(1,0))),((-1,1),(154,(1,0))),((0,-1),(35,(0,1))),((0,2),(29,(0,0))),((1,0),(44,(0,0))),((1,2),(56,(0,0))),((2,0),(60,(0,0))),((2,3),(63,(0,0))),((3,1),(64,(0,0))),((3,2),(65,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_21_checked : successorFastRowCheck layer6 row5_21 row5_21choice = true := by decide
def row5_22 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1)]
def row5_22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(97,(1,0))),((-1,1),(155,(1,0))),((0,-1),(36,(0,1))),((0,2),(30,(0,0))),((1,0),(45,(0,0))),((1,2),(57,(0,0))),((2,0),(62,(0,0))),((2,2),(64,(0,0))),((3,0),(66,(0,0))),((3,2),(67,(0,0))),((4,1),(68,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_22_checked : successorFastRowCheck layer6 row5_22 row5_22choice = true := by decide
def row5_23 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2)]
def row5_23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(98,(1,0))),((-1,2),(193,(1,0))),((0,-1),(37,(0,1))),((0,1),(17,(0,0))),((0,3),(69,(0,0))),((1,-1),(132,(0,1))),((1,3),(70,(0,0))),((2,0),(71,(0,0))),((2,1),(72,(0,0))),((2,2),(73,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_23_checked : successorFastRowCheck layer6 row5_23 row5_23choice = true := by decide
def Closure5C002rows : List (List GridPoint) := [row5_16,row5_17,row5_18,row5_19,row5_20,row5_21,row5_22,row5_23]
theorem Closure5C002_closed : ∀ row ∈ Closure5C002rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C002rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_16choice,row5_16_checked⟩
  · subst row
    exact ⟨row5_17choice,row5_17_checked⟩
  · subst row
    exact ⟨row5_18choice,row5_18_checked⟩
  · subst row
    exact ⟨row5_19choice,row5_19_checked⟩
  · subst row
    exact ⟨row5_20choice,row5_20_checked⟩
  · subst row
    exact ⟨row5_21choice,row5_21_checked⟩
  · subst row
    exact ⟨row5_22choice,row5_22_checked⟩
  · subst row
    exact ⟨row5_23choice,row5_23_checked⟩
end Polyomino57
