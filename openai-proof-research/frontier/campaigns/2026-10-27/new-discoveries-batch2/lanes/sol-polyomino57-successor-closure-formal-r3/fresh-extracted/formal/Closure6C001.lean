import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_8 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3)]
def row6_8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(249,(1,0))),((-1,1),(444,(1,0))),((-1,2),(610,(1,0))),((-1,3),(713,(1,0))),((0,-1),(14,(0,1))),((0,4),(9,(0,0))),((1,-1),(356,(0,1))),((1,1),(24,(0,0))),((1,2),(27,(0,0))),((1,4),(30,(0,0))),((2,0),(31,(0,0))),((2,3),(32,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_8_checked : successorFastRowCheck layer7 row6_8 row6_8choice = true := by decide
def row6_9 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)]
def row6_9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(250,(1,0))),((-1,1),(445,(1,0))),((-1,2),(611,(1,0))),((-1,3),(714,(1,0))),((0,-1),(15,(0,1))),((0,4),(11,(0,0))),((1,-1),(358,(0,1))),((1,1),(25,(0,0))),((1,2),(28,(0,0))),((1,3),(31,(0,0))),((2,-1),(359,(0,1))),((2,1),(33,(0,0))),((3,0),(34,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_9_checked : successorFastRowCheck layer7 row6_9 row6_9choice = true := by decide
def row6_10 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2)]
def row6_10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(251,(1,0))),((-1,1),(446,(1,0))),((-1,2),(612,(1,0))),((-1,3),(715,(1,0))),((0,-1),(16,(0,1))),((0,4),(12,(0,0))),((1,0),(23,(0,0))),((1,3),(35,(0,0))),((2,1),(36,(0,0))),((2,2),(37,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_10_checked : successorFastRowCheck layer7 row6_10 row6_10choice = true := by decide
def row6_11 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3)]
def row6_11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(252,(1,0))),((-1,1),(447,(1,0))),((-1,2),(613,(1,0))),((-1,3),(716,(1,0))),((0,-1),(17,(0,1))),((0,4),(13,(0,0))),((1,0),(24,(0,0))),((1,2),(35,(0,0))),((1,4),(38,(0,0))),((2,1),(39,(0,0))),((2,3),(40,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_11_checked : successorFastRowCheck layer7 row6_11 row6_11choice = true := by decide
def row6_12 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1)]
def row6_12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(253,(1,0))),((-1,1),(448,(1,0))),((-1,2),(614,(1,0))),((-1,3),(717,(1,0))),((0,-1),(18,(0,1))),((0,4),(15,(0,0))),((1,0),(26,(0,0))),((1,2),(36,(0,0))),((1,3),(39,(0,0))),((2,0),(41,(0,0))),((2,2),(42,(0,0))),((3,1),(43,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_12_checked : successorFastRowCheck layer7 row6_12 row6_12choice = true := by decide
def row6_13 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)]
def row6_13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(254,(1,0))),((-1,1),(449,(1,0))),((-1,2),(615,(1,0))),((-1,3),(718,(1,0))),((0,-1),(19,(0,1))),((0,4),(16,(0,0))),((1,0),(27,(0,0))),((1,1),(35,(0,0))),((1,4),(44,(0,0))),((2,2),(45,(0,0))),((2,3),(46,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_13_checked : successorFastRowCheck layer7 row6_13 row6_13choice = true := by decide
def row6_14 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2)]
def row6_14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(255,(1,0))),((-1,1),(450,(1,0))),((-1,2),(616,(1,0))),((-1,3),(719,(1,0))),((0,-1),(20,(0,1))),((0,4),(18,(0,0))),((1,0),(29,(0,0))),((1,1),(37,(0,0))),((1,3),(45,(0,0))),((2,1),(47,(0,0))),((2,3),(48,(0,0))),((3,2),(49,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_14_checked : successorFastRowCheck layer7 row6_14 row6_14choice = true := by decide
def row6_15 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4)]
def row6_15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(256,(1,0))),((-1,1),(451,(1,0))),((-1,2),(617,(1,0))),((-1,3),(720,(1,0))),((0,-1),(21,(0,1))),((0,4),(19,(0,0))),((1,0),(30,(0,0))),((1,1),(38,(0,0))),((1,2),(44,(0,0))),((1,5),(50,(0,0))),((2,3),(51,(0,0))),((2,4),(52,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_15_checked : successorFastRowCheck layer7 row6_15 row6_15choice = true := by decide
def Closure6C001rows : List (List GridPoint) := [row6_8,row6_9,row6_10,row6_11,row6_12,row6_13,row6_14,row6_15]
theorem Closure6C001_closed : ∀ row ∈ Closure6C001rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C001rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_8choice,row6_8_checked⟩
  · subst row
    exact ⟨row6_9choice,row6_9_checked⟩
  · subst row
    exact ⟨row6_10choice,row6_10_checked⟩
  · subst row
    exact ⟨row6_11choice,row6_11_checked⟩
  · subst row
    exact ⟨row6_12choice,row6_12_checked⟩
  · subst row
    exact ⟨row6_13choice,row6_13_checked⟩
  · subst row
    exact ⟨row6_14choice,row6_14_checked⟩
  · subst row
    exact ⟨row6_15choice,row6_15_checked⟩
end Polyomino57
