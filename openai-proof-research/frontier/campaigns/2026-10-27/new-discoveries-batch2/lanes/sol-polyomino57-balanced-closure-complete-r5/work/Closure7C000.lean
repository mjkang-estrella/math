import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_0 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]
def row7_0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(793,(1,0))),((-1,1),(1459,(1,0))),((-1,2),(2047,(1,0))),((-1,3),(2441,(1,0))),((-1,4),(2644,(1,0))),((-1,5),(2712,(1,0))),((-1,6),(2724,(1,0))),((0,-1),(0,(0,1))),((0,7),(0,(0,0))),((1,0),(1,(0,0))),((1,1),(2,(0,0))),((1,2),(3,(0,0))),((1,3),(4,(0,0))),((1,4),(5,(0,0))),((1,5),(6,(0,0))),((1,6),(7,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_0_checked : successorFastRowCheck layer8 row7_0 row7_0choice = true := by decide
def row7_1 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0)]
def row7_1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(794,(1,0))),((-1,1),(1460,(1,0))),((-1,2),(2048,(1,0))),((-1,3),(2442,(1,0))),((-1,4),(2645,(1,0))),((-1,5),(2713,(1,0))),((0,-1),(2,(0,1))),((0,6),(1,(0,0))),((1,-1),(1146,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_1_checked : successorFastRowCheck layer8 row7_1 row7_1choice = true := by decide
def row7_2 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1)]
def row7_2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(795,(1,0))),((-1,1),(1461,(1,0))),((-1,2),(2049,(1,0))),((-1,3),(2443,(1,0))),((-1,4),(2646,(1,0))),((-1,5),(2714,(1,0))),((0,-1),(3,(0,1))),((0,6),(2,(0,0))),((1,0),(8,(0,0))),((1,2),(14,(0,0))),((1,3),(15,(0,0))),((1,4),(16,(0,0))),((1,5),(17,(0,0))),((2,1),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_2_checked : successorFastRowCheck layer8 row7_2 row7_2choice = true := by decide
def row7_3 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2)]
def row7_3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(796,(1,0))),((-1,1),(1462,(1,0))),((-1,2),(2050,(1,0))),((-1,3),(2444,(1,0))),((-1,4),(2647,(1,0))),((-1,5),(2715,(1,0))),((0,-1),(4,(0,1))),((0,6),(3,(0,0))),((1,0),(9,(0,0))),((1,1),(14,(0,0))),((1,3),(19,(0,0))),((1,4),(20,(0,0))),((1,5),(21,(0,0))),((2,2),(22,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_3_checked : successorFastRowCheck layer8 row7_3 row7_3choice = true := by decide
def row7_4 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3)]
def row7_4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(797,(1,0))),((-1,1),(1463,(1,0))),((-1,2),(2051,(1,0))),((-1,3),(2445,(1,0))),((-1,4),(2648,(1,0))),((-1,5),(2716,(1,0))),((0,-1),(5,(0,1))),((0,6),(4,(0,0))),((1,0),(10,(0,0))),((1,1),(15,(0,0))),((1,2),(19,(0,0))),((1,4),(23,(0,0))),((1,5),(24,(0,0))),((2,3),(25,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_4_checked : successorFastRowCheck layer8 row7_4 row7_4choice = true := by decide
def row7_5 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4)]
def row7_5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(798,(1,0))),((-1,1),(1464,(1,0))),((-1,2),(2052,(1,0))),((-1,3),(2446,(1,0))),((-1,4),(2649,(1,0))),((-1,5),(2717,(1,0))),((0,-1),(6,(0,1))),((0,6),(5,(0,0))),((1,0),(11,(0,0))),((1,1),(16,(0,0))),((1,2),(20,(0,0))),((1,3),(23,(0,0))),((1,5),(26,(0,0))),((2,4),(27,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_5_checked : successorFastRowCheck layer8 row7_5 row7_5choice = true := by decide
def row7_6 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5)]
def row7_6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(799,(1,0))),((-1,1),(1465,(1,0))),((-1,2),(2053,(1,0))),((-1,3),(2447,(1,0))),((-1,4),(2650,(1,0))),((-1,5),(2718,(1,0))),((0,-1),(7,(0,1))),((0,6),(6,(0,0))),((1,0),(12,(0,0))),((1,1),(17,(0,0))),((1,2),(21,(0,0))),((1,3),(24,(0,0))),((1,4),(26,(0,0))),((1,6),(28,(0,0))),((2,5),(29,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_6_checked : successorFastRowCheck layer8 row7_6 row7_6choice = true := by decide
def row7_7 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1)]
def row7_7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(800,(1,0))),((-1,1),(1466,(1,0))),((-1,2),(2054,(1,0))),((-1,3),(2448,(1,0))),((-1,4),(2651,(1,0))),((0,-1),(14,(0,1))),((0,5),(8,(0,0))),((1,-1),(1147,(0,1))),((1,2),(30,(0,0))),((1,3),(31,(0,0))),((1,4),(32,(0,0))),((2,0),(33,(0,0))),((2,1),(34,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_7_checked : successorFastRowCheck layer8 row7_7 row7_7choice = true := by decide
def Closure7C000rows : List (List GridPoint) := [row7_0,row7_1,row7_2,row7_3,row7_4,row7_5,row7_6,row7_7]
theorem Closure7C000_closed : ∀ row ∈ Closure7C000rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C000rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_0choice,row7_0_checked⟩
  · subst row
    exact ⟨row7_1choice,row7_1_checked⟩
  · subst row
    exact ⟨row7_2choice,row7_2_checked⟩
  · subst row
    exact ⟨row7_3choice,row7_3_checked⟩
  · subst row
    exact ⟨row7_4choice,row7_4_checked⟩
  · subst row
    exact ⟨row7_5choice,row7_5_checked⟩
  · subst row
    exact ⟨row7_6choice,row7_6_checked⟩
  · subst row
    exact ⟨row7_7choice,row7_7_checked⟩
end Polyomino57
