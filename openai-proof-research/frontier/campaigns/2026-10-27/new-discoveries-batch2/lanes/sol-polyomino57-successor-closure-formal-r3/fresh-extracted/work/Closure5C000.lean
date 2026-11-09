import Layer6
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row5_0 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4)]
def row5_0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(75,(1,0))),((-1,1),(133,(1,0))),((-1,2),(181,(1,0))),((-1,3),(207,(1,0))),((-1,4),(215,(1,0))),((0,-1),(0,(0,1))),((0,5),(0,(0,0))),((1,0),(1,(0,0))),((1,1),(2,(0,0))),((1,2),(3,(0,0))),((1,3),(4,(0,0))),((1,4),(5,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_0_checked : successorFastRowCheck layer6 row5_0 row5_0choice = true := by decide
def row5_1 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0)]
def row5_1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(76,(1,0))),((-1,1),(134,(1,0))),((-1,2),(182,(1,0))),((-1,3),(208,(1,0))),((0,-1),(2,(0,1))),((0,4),(1,(0,0))),((1,-1),(112,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_1_checked : successorFastRowCheck layer6 row5_1 row5_1choice = true := by decide
def row5_2 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1)]
def row5_2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(77,(1,0))),((-1,1),(135,(1,0))),((-1,2),(183,(1,0))),((-1,3),(209,(1,0))),((0,-1),(3,(0,1))),((0,4),(2,(0,0))),((1,0),(6,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((2,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_2_checked : successorFastRowCheck layer6 row5_2 row5_2choice = true := by decide
def row5_3 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2)]
def row5_3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(78,(1,0))),((-1,1),(136,(1,0))),((-1,2),(184,(1,0))),((-1,3),(210,(1,0))),((0,-1),(4,(0,1))),((0,4),(3,(0,0))),((1,0),(7,(0,0))),((1,1),(10,(0,0))),((1,3),(13,(0,0))),((2,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_3_checked : successorFastRowCheck layer6 row5_3 row5_3choice = true := by decide
def row5_4 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3)]
def row5_4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(79,(1,0))),((-1,1),(137,(1,0))),((-1,2),(185,(1,0))),((-1,3),(211,(1,0))),((0,-1),(5,(0,1))),((0,4),(4,(0,0))),((1,0),(8,(0,0))),((1,1),(11,(0,0))),((1,2),(13,(0,0))),((1,4),(15,(0,0))),((2,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_4_checked : successorFastRowCheck layer6 row5_4 row5_4choice = true := by decide
def row5_5 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1)]
def row5_5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(80,(1,0))),((-1,1),(138,(1,0))),((-1,2),(186,(1,0))),((0,-1),(10,(0,1))),((0,3),(6,(0,0))),((1,-1),(113,(0,1))),((1,2),(17,(0,0))),((2,0),(18,(0,0))),((2,1),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_5_checked : successorFastRowCheck layer6 row5_5 row5_5choice = true := by decide
def row5_6 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2)]
def row5_6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(81,(1,0))),((-1,1),(139,(1,0))),((-1,2),(187,(1,0))),((0,-1),(11,(0,1))),((0,3),(7,(0,0))),((1,-1),(114,(0,1))),((1,1),(17,(0,0))),((1,3),(20,(0,0))),((2,0),(21,(0,0))),((2,2),(22,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_6_checked : successorFastRowCheck layer6 row5_6 row5_6choice = true := by decide
def row5_7 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0)]
def row5_7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(82,(1,0))),((-1,1),(140,(1,0))),((-1,2),(188,(1,0))),((0,-1),(12,(0,1))),((0,3),(9,(0,0))),((1,-1),(116,(0,1))),((1,1),(18,(0,0))),((1,2),(21,(0,0))),((2,-1),(117,(0,1))),((2,1),(23,(0,0))),((3,0),(24,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row5_7_checked : successorFastRowCheck layer6 row5_7 row5_7choice = true := by decide
def Closure5C000rows : List (List GridPoint) := [row5_0,row5_1,row5_2,row5_3,row5_4,row5_5,row5_6,row5_7]
theorem Closure5C000_closed : ∀ row ∈ Closure5C000rows, ∃ choice, successorFastRowCheck layer6 row choice = true := by
  intro row hr
  simp only [Closure5C000rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row5_0choice,row5_0_checked⟩
  · subst row
    exact ⟨row5_1choice,row5_1_checked⟩
  · subst row
    exact ⟨row5_2choice,row5_2_checked⟩
  · subst row
    exact ⟨row5_3choice,row5_3_checked⟩
  · subst row
    exact ⟨row5_4choice,row5_4_checked⟩
  · subst row
    exact ⟨row5_5choice,row5_5_checked⟩
  · subst row
    exact ⟨row5_6choice,row5_6_checked⟩
  · subst row
    exact ⟨row5_7choice,row5_7_checked⟩
end Polyomino57
