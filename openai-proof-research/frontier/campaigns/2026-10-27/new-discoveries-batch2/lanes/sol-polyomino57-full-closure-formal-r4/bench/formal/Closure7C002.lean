import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_16 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3)]
def row7_16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(809,(1,0))),((-1,1),(1475,(1,0))),((-1,2),(2063,(1,0))),((-1,3),(2457,(1,0))),((-1,4),(2660,(1,0))),((0,-1),(23,(0,1))),((0,5),(19,(0,0))),((1,0),(35,(0,0))),((1,1),(47,(0,0))),((1,4),(60,(0,0))),((2,2),(61,(0,0))),((2,3),(62,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_16_checked : successorFastRowCheck layer8 row7_16 row7_16choice = true := by decide
def row7_17 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4)]
def row7_17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(810,(1,0))),((-1,1),(1476,(1,0))),((-1,2),(2064,(1,0))),((-1,3),(2458,(1,0))),((-1,4),(2661,(1,0))),((0,-1),(24,(0,1))),((0,5),(20,(0,0))),((1,0),(36,(0,0))),((1,1),(48,(0,0))),((1,3),(60,(0,0))),((1,5),(63,(0,0))),((2,2),(64,(0,0))),((2,4),(65,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_17_checked : successorFastRowCheck layer8 row7_17 row7_17choice = true := by decide
def row7_18 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2)]
def row7_18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(811,(1,0))),((-1,1),(1477,(1,0))),((-1,2),(2065,(1,0))),((-1,3),(2459,(1,0))),((-1,4),(2662,(1,0))),((0,-1),(25,(0,1))),((0,5),(22,(0,0))),((1,0),(38,(0,0))),((1,1),(50,(0,0))),((1,3),(61,(0,0))),((1,4),(64,(0,0))),((2,1),(66,(0,0))),((2,3),(67,(0,0))),((3,2),(68,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_18_checked : successorFastRowCheck layer8 row7_18 row7_18choice = true := by decide
def row7_19 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4)]
def row7_19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(812,(1,0))),((-1,1),(1478,(1,0))),((-1,2),(2066,(1,0))),((-1,3),(2460,(1,0))),((-1,4),(2663,(1,0))),((0,-1),(26,(0,1))),((0,5),(23,(0,0))),((1,0),(39,(0,0))),((1,1),(51,(0,0))),((1,2),(60,(0,0))),((1,5),(69,(0,0))),((2,3),(70,(0,0))),((2,4),(71,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_19_checked : successorFastRowCheck layer8 row7_19 row7_19choice = true := by decide
def row7_20 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3)]
def row7_20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(813,(1,0))),((-1,1),(1479,(1,0))),((-1,2),(2067,(1,0))),((-1,3),(2461,(1,0))),((-1,4),(2664,(1,0))),((0,-1),(27,(0,1))),((0,5),(25,(0,0))),((1,0),(41,(0,0))),((1,1),(53,(0,0))),((1,2),(62,(0,0))),((1,4),(70,(0,0))),((2,2),(72,(0,0))),((2,4),(73,(0,0))),((3,3),(74,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_20_checked : successorFastRowCheck layer8 row7_20 row7_20choice = true := by decide
def row7_21 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5)]
def row7_21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(814,(1,0))),((-1,1),(1480,(1,0))),((-1,2),(2068,(1,0))),((-1,3),(2462,(1,0))),((-1,4),(2665,(1,0))),((0,-1),(28,(0,1))),((0,5),(26,(0,0))),((1,0),(42,(0,0))),((1,1),(54,(0,0))),((1,2),(63,(0,0))),((1,3),(69,(0,0))),((1,6),(75,(0,0))),((2,4),(76,(0,0))),((2,5),(77,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_21_checked : successorFastRowCheck layer8 row7_21 row7_21choice = true := by decide
def row7_22 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4)]
def row7_22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(815,(1,0))),((-1,1),(1481,(1,0))),((-1,2),(2069,(1,0))),((-1,3),(2463,(1,0))),((-1,4),(2666,(1,0))),((0,-1),(29,(0,1))),((0,5),(27,(0,0))),((1,0),(44,(0,0))),((1,1),(56,(0,0))),((1,2),(65,(0,0))),((1,3),(71,(0,0))),((1,5),(76,(0,0))),((2,3),(78,(0,0))),((2,5),(79,(0,0))),((3,4),(80,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_22_checked : successorFastRowCheck layer8 row7_22 row7_22choice = true := by decide
def row7_23 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2)]
def row7_23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(816,(1,0))),((-1,1),(1482,(1,0))),((-1,2),(2070,(1,0))),((-1,3),(2464,(1,0))),((0,-1),(47,(0,1))),((0,4),(30,(0,0))),((1,-1),(1154,(0,1))),((1,3),(82,(0,0))),((2,0),(83,(0,0))),((2,1),(84,(0,0))),((2,2),(85,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_23_checked : successorFastRowCheck layer8 row7_23 row7_23choice = true := by decide
def Closure7C002rows : List (List GridPoint) := [row7_16,row7_17,row7_18,row7_19,row7_20,row7_21,row7_22,row7_23]
theorem Closure7C002_closed : ∀ row ∈ Closure7C002rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C002rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_16choice,row7_16_checked⟩
  · subst row
    exact ⟨row7_17choice,row7_17_checked⟩
  · subst row
    exact ⟨row7_18choice,row7_18_checked⟩
  · subst row
    exact ⟨row7_19choice,row7_19_checked⟩
  · subst row
    exact ⟨row7_20choice,row7_20_checked⟩
  · subst row
    exact ⟨row7_21choice,row7_21_checked⟩
  · subst row
    exact ⟨row7_22choice,row7_22_checked⟩
  · subst row
    exact ⟨row7_23choice,row7_23_checked⟩
end Polyomino57
