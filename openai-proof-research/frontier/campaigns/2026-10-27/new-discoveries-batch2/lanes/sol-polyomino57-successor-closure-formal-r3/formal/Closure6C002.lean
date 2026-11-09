import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_16 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3)]
def row6_16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(257,(1,0))),((-1,1),(452,(1,0))),((-1,2),(618,(1,0))),((-1,3),(721,(1,0))),((0,-1),(22,(0,1))),((0,4),(20,(0,0))),((1,0),(32,(0,0))),((1,1),(40,(0,0))),((1,2),(46,(0,0))),((1,4),(51,(0,0))),((2,2),(53,(0,0))),((2,4),(54,(0,0))),((3,3),(55,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_16_checked : successorFastRowCheck layer7 row6_16 row6_16choice = true := by decide
def row6_17 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)]
def row6_17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(258,(1,0))),((-1,1),(453,(1,0))),((-1,2),(619,(1,0))),((0,-1),(35,(0,1))),((0,3),(23,(0,0))),((1,-1),(360,(0,1))),((1,3),(57,(0,0))),((2,0),(58,(0,0))),((2,1),(59,(0,0))),((2,2),(60,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_17_checked : successorFastRowCheck layer7 row6_17 row6_17choice = true := by decide
def row6_18 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)]
def row6_18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(259,(1,0))),((-1,1),(454,(1,0))),((-1,2),(620,(1,0))),((0,-1),(36,(0,1))),((0,3),(25,(0,0))),((1,-1),(362,(0,1))),((1,2),(58,(0,0))),((2,-1),(372,(0,1))),((2,1),(61,(0,0))),((3,0),(62,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_18_checked : successorFastRowCheck layer7 row6_18 row6_18choice = true := by decide
def row6_19 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1)]
def row6_19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(260,(1,0))),((-1,1),(455,(1,0))),((-1,2),(621,(1,0))),((0,-1),(37,(0,1))),((0,3),(26,(0,0))),((1,-1),(363,(0,1))),((1,2),(59,(0,0))),((2,0),(61,(0,0))),((2,2),(63,(0,0))),((3,1),(64,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_19_checked : successorFastRowCheck layer7 row6_19 row6_19choice = true := by decide
def row6_20 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3)]
def row6_20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(261,(1,0))),((-1,1),(456,(1,0))),((-1,2),(622,(1,0))),((0,-1),(38,(0,1))),((0,3),(27,(0,0))),((1,-1),(364,(0,1))),((1,1),(57,(0,0))),((1,4),(65,(0,0))),((2,0),(66,(0,0))),((2,2),(67,(0,0))),((2,3),(68,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_20_checked : successorFastRowCheck layer7 row6_20 row6_20choice = true := by decide
def row6_21 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0)]
def row6_21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(262,(1,0))),((-1,1),(457,(1,0))),((-1,2),(623,(1,0))),((0,-1),(39,(0,1))),((0,3),(28,(0,0))),((1,-1),(366,(0,1))),((1,1),(58,(0,0))),((1,3),(66,(0,0))),((2,-1),(373,(0,1))),((2,1),(69,(0,0))),((2,2),(70,(0,0))),((3,0),(71,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_21_checked : successorFastRowCheck layer7 row6_21 row6_21choice = true := by decide
def row6_22 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2)]
def row6_22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(263,(1,0))),((-1,1),(458,(1,0))),((-1,2),(624,(1,0))),((0,-1),(40,(0,1))),((0,3),(29,(0,0))),((1,-1),(367,(0,1))),((1,1),(60,(0,0))),((1,3),(67,(0,0))),((2,0),(70,(0,0))),((2,1),(72,(0,0))),((2,3),(73,(0,0))),((3,2),(74,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_22_checked : successorFastRowCheck layer7 row6_22 row6_22choice = true := by decide
def row6_23 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1)]
def row6_23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(264,(1,0))),((-1,1),(459,(1,0))),((-1,2),(625,(1,0))),((0,-1),(42,(0,1))),((0,3),(33,(0,0))),((1,-1),(370,(0,1))),((1,1),(61,(0,0))),((1,2),(69,(0,0))),((2,-1),(374,(0,1))),((2,2),(75,(0,0))),((3,0),(76,(0,0))),((3,1),(77,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_23_checked : successorFastRowCheck layer7 row6_23 row6_23choice = true := by decide
def Closure6C002rows : List (List GridPoint) := [row6_16,row6_17,row6_18,row6_19,row6_20,row6_21,row6_22,row6_23]
theorem Closure6C002_closed : ∀ row ∈ Closure6C002rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C002rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_16choice,row6_16_checked⟩
  · subst row
    exact ⟨row6_17choice,row6_17_checked⟩
  · subst row
    exact ⟨row6_18choice,row6_18_checked⟩
  · subst row
    exact ⟨row6_19choice,row6_19_checked⟩
  · subst row
    exact ⟨row6_20choice,row6_20_checked⟩
  · subst row
    exact ⟨row6_21choice,row6_21_checked⟩
  · subst row
    exact ⟨row6_22choice,row6_22_checked⟩
  · subst row
    exact ⟨row6_23choice,row6_23_checked⟩
end Polyomino57
