import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_472 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def row7_472choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1794,(1,0))),((0,0),(447,(0,0))),((0,2),(1286,(0,0))),((1,-1),(2102,(0,1))),((1,3),(1508,(0,0))),((2,0),(1533,(0,0))),((2,1),(1547,(0,0))),((2,3),(1563,(0,0))),((3,1),(1569,(0,0))),((3,3),(1571,(0,0))),((4,1),(1573,(0,0))),((4,3),(1574,(0,0))),((5,2),(1575,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_472_checked : successorFastRowCheck layer8 row7_472 row7_472choice = true := by decide
def row7_473 : List GridPoint := [(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def row7_473choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1795,(1,0))),((0,0),(448,(0,0))),((0,2),(1287,(0,0))),((0,3),(1442,(0,0))),((1,-1),(2103,(0,1))),((1,2),(1494,(0,0))),((1,4),(1576,(0,0))),((2,0),(1577,(0,0))),((2,4),(1578,(0,0))),((3,1),(1579,(0,0))),((3,2),(1580,(0,0))),((3,3),(1581,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_473_checked : successorFastRowCheck layer8 row7_473 row7_473choice = true := by decide
def row7_474 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)]
def row7_474choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1796,(1,0))),((0,0),(449,(0,0))),((0,2),(1288,(0,0))),((1,-1),(2127,(0,1))),((1,2),(1516,(0,0))),((1,3),(1577,(0,0))),((2,-1),(2208,(0,1))),((2,4),(1583,(0,0))),((3,0),(1584,(0,0))),((3,1),(1585,(0,0))),((3,2),(1586,(0,0))),((3,3),(1587,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_474_checked : successorFastRowCheck layer8 row7_474 row7_474choice = true := by decide
def row7_475 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)]
def row7_475choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1797,(1,0))),((0,0),(450,(0,0))),((0,2),(1289,(0,0))),((1,-1),(2128,(0,1))),((1,2),(1517,(0,0))),((2,-1),(2210,(0,1))),((2,3),(1584,(0,0))),((3,-1),(2232,(0,1))),((3,1),(1588,(0,0))),((3,2),(1589,(0,0))),((4,0),(1590,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_475_checked : successorFastRowCheck layer8 row7_475 row7_475choice = true := by decide
def row7_476 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)]
def row7_476choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1798,(1,0))),((0,0),(451,(0,0))),((0,2),(1290,(0,0))),((1,-1),(2129,(0,1))),((1,2),(1518,(0,0))),((2,-1),(2211,(0,1))),((2,3),(1585,(0,0))),((3,0),(1588,(0,0))),((3,2),(1591,(0,0))),((4,1),(1592,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_476_checked : successorFastRowCheck layer8 row7_476 row7_476choice = true := by decide
def row7_477 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]
def row7_477choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1799,(1,0))),((0,0),(452,(0,0))),((0,2),(1291,(0,0))),((1,-1),(2130,(0,1))),((1,2),(1519,(0,0))),((2,-1),(2212,(0,1))),((2,3),(1586,(0,0))),((3,0),(1589,(0,0))),((3,1),(1591,(0,0))),((3,3),(1593,(0,0))),((4,2),(1594,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_477_checked : successorFastRowCheck layer8 row7_477 row7_477choice = true := by decide
def row7_478 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
def row7_478choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1800,(1,0))),((0,0),(453,(0,0))),((0,2),(1292,(0,0))),((1,-1),(2132,(0,1))),((1,2),(1520,(0,0))),((2,-1),(2216,(0,1))),((2,2),(1588,(0,0))),((3,-1),(2233,(0,1))),((3,2),(1595,(0,0))),((4,0),(1596,(0,0))),((4,1),(1597,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_478_checked : successorFastRowCheck layer8 row7_478 row7_478choice = true := by decide
def row7_479 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]
def row7_479choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1801,(1,0))),((0,0),(454,(0,0))),((0,2),(1293,(0,0))),((1,-1),(2133,(0,1))),((1,2),(1521,(0,0))),((2,-1),(2217,(0,1))),((2,2),(1590,(0,0))),((3,-1),(2235,(0,1))),((3,1),(1596,(0,0))),((4,-1),(2236,(0,1))),((4,1),(1598,(0,0))),((5,0),(1599,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_479_checked : successorFastRowCheck layer8 row7_479 row7_479choice = true := by decide
def Closure7C059rows : List (List GridPoint) := [row7_472,row7_473,row7_474,row7_475,row7_476,row7_477,row7_478,row7_479]
theorem Closure7C059_closed : ∀ row ∈ Closure7C059rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C059rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_472choice,row7_472_checked⟩
  · subst row
    exact ⟨row7_473choice,row7_473_checked⟩
  · subst row
    exact ⟨row7_474choice,row7_474_checked⟩
  · subst row
    exact ⟨row7_475choice,row7_475_checked⟩
  · subst row
    exact ⟨row7_476choice,row7_476_checked⟩
  · subst row
    exact ⟨row7_477choice,row7_477_checked⟩
  · subst row
    exact ⟨row7_478choice,row7_478_checked⟩
  · subst row
    exact ⟨row7_479choice,row7_479_checked⟩
end Polyomino57
