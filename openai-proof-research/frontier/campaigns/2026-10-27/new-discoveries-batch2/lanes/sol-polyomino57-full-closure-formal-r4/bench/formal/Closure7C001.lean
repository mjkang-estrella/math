import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_8 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2)]
def row7_8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(801,(1,0))),((-1,1),(1467,(1,0))),((-1,2),(2055,(1,0))),((-1,3),(2449,(1,0))),((-1,4),(2652,(1,0))),((0,-1),(15,(0,1))),((0,5),(9,(0,0))),((1,-1),(1148,(0,1))),((1,1),(30,(0,0))),((1,3),(35,(0,0))),((1,4),(36,(0,0))),((2,0),(37,(0,0))),((2,2),(38,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_8_checked : successorFastRowCheck layer8 row7_8 row7_8choice = true := by decide
def row7_9 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3)]
def row7_9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(802,(1,0))),((-1,1),(1468,(1,0))),((-1,2),(2056,(1,0))),((-1,3),(2450,(1,0))),((-1,4),(2653,(1,0))),((0,-1),(16,(0,1))),((0,5),(10,(0,0))),((1,-1),(1149,(0,1))),((1,1),(31,(0,0))),((1,2),(35,(0,0))),((1,4),(39,(0,0))),((2,0),(40,(0,0))),((2,3),(41,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_9_checked : successorFastRowCheck layer8 row7_9 row7_9choice = true := by decide
def row7_10 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4)]
def row7_10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(803,(1,0))),((-1,1),(1469,(1,0))),((-1,2),(2057,(1,0))),((-1,3),(2451,(1,0))),((-1,4),(2654,(1,0))),((0,-1),(17,(0,1))),((0,5),(11,(0,0))),((1,-1),(1150,(0,1))),((1,1),(32,(0,0))),((1,2),(36,(0,0))),((1,3),(39,(0,0))),((1,5),(42,(0,0))),((2,0),(43,(0,0))),((2,4),(44,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_10_checked : successorFastRowCheck layer8 row7_10 row7_10choice = true := by decide
def row7_11 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0)]
def row7_11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(804,(1,0))),((-1,1),(1470,(1,0))),((-1,2),(2058,(1,0))),((-1,3),(2452,(1,0))),((-1,4),(2655,(1,0))),((0,-1),(18,(0,1))),((0,5),(13,(0,0))),((1,-1),(1152,(0,1))),((1,1),(33,(0,0))),((1,2),(37,(0,0))),((1,3),(40,(0,0))),((1,4),(43,(0,0))),((2,-1),(1153,(0,1))),((2,1),(45,(0,0))),((3,0),(46,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_11_checked : successorFastRowCheck layer8 row7_11 row7_11choice = true := by decide
def row7_12 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2)]
def row7_12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(805,(1,0))),((-1,1),(1471,(1,0))),((-1,2),(2059,(1,0))),((-1,3),(2453,(1,0))),((-1,4),(2656,(1,0))),((0,-1),(19,(0,1))),((0,5),(14,(0,0))),((1,0),(30,(0,0))),((1,3),(47,(0,0))),((1,4),(48,(0,0))),((2,1),(49,(0,0))),((2,2),(50,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_12_checked : successorFastRowCheck layer8 row7_12 row7_12choice = true := by decide
def row7_13 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3)]
def row7_13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(806,(1,0))),((-1,1),(1472,(1,0))),((-1,2),(2060,(1,0))),((-1,3),(2454,(1,0))),((-1,4),(2657,(1,0))),((0,-1),(20,(0,1))),((0,5),(15,(0,0))),((1,0),(31,(0,0))),((1,2),(47,(0,0))),((1,4),(51,(0,0))),((2,1),(52,(0,0))),((2,3),(53,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_13_checked : successorFastRowCheck layer8 row7_13 row7_13choice = true := by decide
def row7_14 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4)]
def row7_14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(807,(1,0))),((-1,1),(1473,(1,0))),((-1,2),(2061,(1,0))),((-1,3),(2455,(1,0))),((-1,4),(2658,(1,0))),((0,-1),(21,(0,1))),((0,5),(16,(0,0))),((1,0),(32,(0,0))),((1,2),(48,(0,0))),((1,3),(51,(0,0))),((1,5),(54,(0,0))),((2,1),(55,(0,0))),((2,4),(56,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_14_checked : successorFastRowCheck layer8 row7_14 row7_14choice = true := by decide
def row7_15 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1)]
def row7_15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(808,(1,0))),((-1,1),(1474,(1,0))),((-1,2),(2062,(1,0))),((-1,3),(2456,(1,0))),((-1,4),(2659,(1,0))),((0,-1),(22,(0,1))),((0,5),(18,(0,0))),((1,0),(34,(0,0))),((1,2),(49,(0,0))),((1,3),(52,(0,0))),((1,4),(55,(0,0))),((2,0),(57,(0,0))),((2,2),(58,(0,0))),((3,1),(59,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_15_checked : successorFastRowCheck layer8 row7_15 row7_15choice = true := by decide
def Closure7C001rows : List (List GridPoint) := [row7_8,row7_9,row7_10,row7_11,row7_12,row7_13,row7_14,row7_15]
theorem Closure7C001_closed : ∀ row ∈ Closure7C001rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C001rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_8choice,row7_8_checked⟩
  · subst row
    exact ⟨row7_9choice,row7_9_checked⟩
  · subst row
    exact ⟨row7_10choice,row7_10_checked⟩
  · subst row
    exact ⟨row7_11choice,row7_11_checked⟩
  · subst row
    exact ⟨row7_12choice,row7_12_checked⟩
  · subst row
    exact ⟨row7_13choice,row7_13_checked⟩
  · subst row
    exact ⟨row7_14choice,row7_14_checked⟩
  · subst row
    exact ⟨row7_15choice,row7_15_checked⟩
end Polyomino57
