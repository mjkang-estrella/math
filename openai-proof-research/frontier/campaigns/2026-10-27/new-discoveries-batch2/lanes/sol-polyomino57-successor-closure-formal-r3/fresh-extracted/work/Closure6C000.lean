import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_0 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5)]
def row6_0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(241,(1,0))),((-1,1),(436,(1,0))),((-1,2),(602,(1,0))),((-1,3),(705,(1,0))),((-1,4),(749,(1,0))),((-1,5),(759,(1,0))),((0,-1),(0,(0,1))),((0,6),(0,(0,0))),((1,0),(1,(0,0))),((1,1),(2,(0,0))),((1,2),(3,(0,0))),((1,3),(4,(0,0))),((1,4),(5,(0,0))),((1,5),(6,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_0_checked : successorFastRowCheck layer7 row6_0 row6_0choice = true := by decide
def row6_1 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0)]
def row6_1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(242,(1,0))),((-1,1),(437,(1,0))),((-1,2),(603,(1,0))),((-1,3),(706,(1,0))),((-1,4),(750,(1,0))),((0,-1),(2,(0,1))),((0,5),(1,(0,0))),((1,-1),(353,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_1_checked : successorFastRowCheck layer7 row6_1 row6_1choice = true := by decide
def row6_2 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1)]
def row6_2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(243,(1,0))),((-1,1),(438,(1,0))),((-1,2),(604,(1,0))),((-1,3),(707,(1,0))),((-1,4),(751,(1,0))),((0,-1),(3,(0,1))),((0,5),(2,(0,0))),((1,0),(7,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((2,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_2_checked : successorFastRowCheck layer7 row6_2 row6_2choice = true := by decide
def row6_3 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2)]
def row6_3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(244,(1,0))),((-1,1),(439,(1,0))),((-1,2),(605,(1,0))),((-1,3),(708,(1,0))),((-1,4),(752,(1,0))),((0,-1),(4,(0,1))),((0,5),(3,(0,0))),((1,0),(8,(0,0))),((1,1),(12,(0,0))),((1,3),(16,(0,0))),((1,4),(17,(0,0))),((2,2),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_3_checked : successorFastRowCheck layer7 row6_3 row6_3choice = true := by decide
def row6_4 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3)]
def row6_4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(245,(1,0))),((-1,1),(440,(1,0))),((-1,2),(606,(1,0))),((-1,3),(709,(1,0))),((-1,4),(753,(1,0))),((0,-1),(5,(0,1))),((0,5),(4,(0,0))),((1,0),(9,(0,0))),((1,1),(13,(0,0))),((1,2),(16,(0,0))),((1,4),(19,(0,0))),((2,3),(20,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_4_checked : successorFastRowCheck layer7 row6_4 row6_4choice = true := by decide
def row6_5 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4)]
def row6_5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(246,(1,0))),((-1,1),(441,(1,0))),((-1,2),(607,(1,0))),((-1,3),(710,(1,0))),((-1,4),(754,(1,0))),((0,-1),(6,(0,1))),((0,5),(5,(0,0))),((1,0),(10,(0,0))),((1,1),(14,(0,0))),((1,2),(17,(0,0))),((1,3),(19,(0,0))),((1,5),(21,(0,0))),((2,4),(22,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_5_checked : successorFastRowCheck layer7 row6_5 row6_5choice = true := by decide
def row6_6 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)]
def row6_6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(247,(1,0))),((-1,1),(442,(1,0))),((-1,2),(608,(1,0))),((-1,3),(711,(1,0))),((0,-1),(12,(0,1))),((0,4),(7,(0,0))),((1,-1),(354,(0,1))),((1,2),(23,(0,0))),((1,3),(24,(0,0))),((2,0),(25,(0,0))),((2,1),(26,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_6_checked : successorFastRowCheck layer7 row6_6 row6_6choice = true := by decide
def row6_7 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2)]
def row6_7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(248,(1,0))),((-1,1),(443,(1,0))),((-1,2),(609,(1,0))),((-1,3),(712,(1,0))),((0,-1),(13,(0,1))),((0,4),(8,(0,0))),((1,-1),(355,(0,1))),((1,1),(23,(0,0))),((1,3),(27,(0,0))),((2,0),(28,(0,0))),((2,2),(29,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_7_checked : successorFastRowCheck layer7 row6_7 row6_7choice = true := by decide
def Closure6C000rows : List (List GridPoint) := [row6_0,row6_1,row6_2,row6_3,row6_4,row6_5,row6_6,row6_7]
theorem Closure6C000_closed : ∀ row ∈ Closure6C000rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C000rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_0choice,row6_0_checked⟩
  · subst row
    exact ⟨row6_1choice,row6_1_checked⟩
  · subst row
    exact ⟨row6_2choice,row6_2_checked⟩
  · subst row
    exact ⟨row6_3choice,row6_3_checked⟩
  · subst row
    exact ⟨row6_4choice,row6_4_checked⟩
  · subst row
    exact ⟨row6_5choice,row6_5_checked⟩
  · subst row
    exact ⟨row6_6choice,row6_6_checked⟩
  · subst row
    exact ⟨row6_7choice,row6_7_checked⟩
end Polyomino57
