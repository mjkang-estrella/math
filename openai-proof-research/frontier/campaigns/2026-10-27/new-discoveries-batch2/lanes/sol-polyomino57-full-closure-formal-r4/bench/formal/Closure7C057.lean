import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_456 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def row7_456choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1778,(1,0))),((0,0),(431,(0,0))),((0,2),(1270,(0,0))),((1,-1),(2085,(0,1))),((1,3),(1486,(0,0))),((2,-1),(2193,(0,1))),((2,1),(1516,(0,0))),((2,4),(1524,(0,0))),((3,0),(1525,(0,0))),((3,2),(1526,(0,0))),((3,3),(1527,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_456_checked : successorFastRowCheck layer8 row7_456 row7_456choice = true := by decide
def row7_457 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def row7_457choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1779,(1,0))),((0,0),(432,(0,0))),((0,2),(1271,(0,0))),((1,-1),(2086,(0,1))),((1,3),(1487,(0,0))),((2,-1),(2195,(0,1))),((2,1),(1517,(0,0))),((2,3),(1525,(0,0))),((3,-1),(2202,(0,1))),((3,1),(1528,(0,0))),((3,2),(1529,(0,0))),((4,0),(1530,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_457_checked : successorFastRowCheck layer8 row7_457 row7_457choice = true := by decide
def row7_458 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def row7_458choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1780,(1,0))),((0,0),(433,(0,0))),((0,2),(1272,(0,0))),((1,-1),(2087,(0,1))),((1,3),(1488,(0,0))),((2,-1),(2196,(0,1))),((2,1),(1519,(0,0))),((2,3),(1526,(0,0))),((3,0),(1529,(0,0))),((3,1),(1531,(0,0))),((3,3),(1532,(0,0))),((4,2),(1533,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_458_checked : successorFastRowCheck layer8 row7_458 row7_458choice = true := by decide
def row7_459 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def row7_459choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1781,(1,0))),((0,0),(434,(0,0))),((0,2),(1273,(0,0))),((1,-1),(2089,(0,1))),((1,3),(1492,(0,0))),((2,-1),(2199,(0,1))),((2,1),(1520,(0,0))),((2,2),(1528,(0,0))),((3,-1),(2203,(0,1))),((3,2),(1534,(0,0))),((4,0),(1535,(0,0))),((4,1),(1536,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_459_checked : successorFastRowCheck layer8 row7_459 row7_459choice = true := by decide
def row7_460 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def row7_460choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1782,(1,0))),((0,0),(435,(0,0))),((0,2),(1274,(0,0))),((1,-1),(2090,(0,1))),((1,3),(1493,(0,0))),((2,-1),(2200,(0,1))),((2,1),(1521,(0,0))),((2,2),(1530,(0,0))),((3,-1),(2205,(0,1))),((3,1),(1535,(0,0))),((4,-1),(2206,(0,1))),((4,1),(1537,(0,0))),((5,0),(1538,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_460_checked : successorFastRowCheck layer8 row7_460 row7_460choice = true := by decide
def row7_461 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def row7_461choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1783,(1,0))),((0,0),(436,(0,0))),((0,2),(1275,(0,0))),((1,-1),(2091,(0,1))),((1,3),(1494,(0,0))),((2,0),(1516,(0,0))),((2,4),(1539,(0,0))),((3,1),(1540,(0,0))),((3,2),(1541,(0,0))),((3,3),(1542,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_461_checked : successorFastRowCheck layer8 row7_461 row7_461choice = true := by decide
def row7_462 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def row7_462choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1784,(1,0))),((0,0),(437,(0,0))),((0,2),(1276,(0,0))),((1,-1),(2092,(0,1))),((1,3),(1495,(0,0))),((2,0),(1518,(0,0))),((2,3),(1540,(0,0))),((3,0),(1543,(0,0))),((3,2),(1544,(0,0))),((4,1),(1545,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_462_checked : successorFastRowCheck layer8 row7_462 row7_462choice = true := by decide
def row7_463 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def row7_463choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1785,(1,0))),((0,0),(438,(0,0))),((0,2),(1277,(0,0))),((1,-1),(2093,(0,1))),((1,3),(1496,(0,0))),((2,0),(1519,(0,0))),((2,3),(1541,(0,0))),((3,1),(1544,(0,0))),((3,3),(1546,(0,0))),((4,2),(1547,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_463_checked : successorFastRowCheck layer8 row7_463 row7_463choice = true := by decide
def Closure7C057rows : List (List GridPoint) := [row7_456,row7_457,row7_458,row7_459,row7_460,row7_461,row7_462,row7_463]
theorem Closure7C057_closed : ∀ row ∈ Closure7C057rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C057rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_456choice,row7_456_checked⟩
  · subst row
    exact ⟨row7_457choice,row7_457_checked⟩
  · subst row
    exact ⟨row7_458choice,row7_458_checked⟩
  · subst row
    exact ⟨row7_459choice,row7_459_checked⟩
  · subst row
    exact ⟨row7_460choice,row7_460_checked⟩
  · subst row
    exact ⟨row7_461choice,row7_461_checked⟩
  · subst row
    exact ⟨row7_462choice,row7_462_checked⟩
  · subst row
    exact ⟨row7_463choice,row7_463_checked⟩
end Polyomino57
