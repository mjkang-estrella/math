import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_464 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_464choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1786,(1,0))),((0,0),(439,(0,0))),((0,2),(1278,(0,0))),((1,-1),(2094,(0,1))),((1,3),(1500,(0,0))),((2,0),(1520,(0,0))),((2,2),(1543,(0,0))),((3,-1),(2207,(0,1))),((3,2),(1548,(0,0))),((4,0),(1549,(0,0))),((4,1),(1550,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_464_checked : successorFastRowCheck layer8 row7_464 row7_464choice = true := by decide
def row7_465 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def row7_465choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1787,(1,0))),((0,0),(440,(0,0))),((0,2),(1279,(0,0))),((1,-1),(2095,(0,1))),((1,3),(1501,(0,0))),((2,0),(1522,(0,0))),((2,2),(1544,(0,0))),((3,0),(1548,(0,0))),((3,3),(1551,(0,0))),((4,1),(1552,(0,0))),((4,2),(1553,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_465_checked : successorFastRowCheck layer8 row7_465 row7_465choice = true := by decide
def row7_466 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def row7_466choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1788,(1,0))),((0,0),(441,(0,0))),((0,2),(1280,(0,0))),((1,-1),(2096,(0,1))),((1,3),(1502,(0,0))),((2,0),(1523,(0,0))),((2,2),(1545,(0,0))),((3,0),(1550,(0,0))),((3,2),(1552,(0,0))),((4,0),(1554,(0,0))),((4,2),(1555,(0,0))),((5,1),(1556,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_466_checked : successorFastRowCheck layer8 row7_466 row7_466choice = true := by decide
def row7_467 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def row7_467choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1789,(1,0))),((0,0),(442,(0,0))),((0,2),(1281,(0,0))),((1,-1),(2097,(0,1))),((1,3),(1503,(0,0))),((1,4),(1515,(0,0))),((2,0),(1524,(0,0))),((2,1),(1539,(0,0))),((2,5),(1557,(0,0))),((3,2),(1558,(0,0))),((3,3),(1559,(0,0))),((3,4),(1560,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_467_checked : successorFastRowCheck layer8 row7_467 row7_467choice = true := by decide
def row7_468 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def row7_468choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1790,(1,0))),((0,0),(443,(0,0))),((0,2),(1282,(0,0))),((1,-1),(2098,(0,1))),((1,3),(1504,(0,0))),((2,0),(1526,(0,0))),((2,1),(1541,(0,0))),((2,4),(1558,(0,0))),((3,1),(1561,(0,0))),((3,3),(1562,(0,0))),((4,2),(1563,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_468_checked : successorFastRowCheck layer8 row7_468 row7_468choice = true := by decide
def row7_469 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def row7_469choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1791,(1,0))),((0,0),(444,(0,0))),((0,2),(1283,(0,0))),((1,-1),(2099,(0,1))),((1,3),(1505,(0,0))),((2,0),(1527,(0,0))),((2,1),(1542,(0,0))),((2,4),(1559,(0,0))),((3,2),(1562,(0,0))),((3,4),(1564,(0,0))),((4,3),(1565,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_469_checked : successorFastRowCheck layer8 row7_469 row7_469choice = true := by decide
def row7_470 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def row7_470choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1792,(1,0))),((0,0),(445,(0,0))),((0,2),(1284,(0,0))),((1,-1),(2100,(0,1))),((1,3),(1506,(0,0))),((2,0),(1531,(0,0))),((2,1),(1544,(0,0))),((2,3),(1561,(0,0))),((3,0),(1566,(0,0))),((3,3),(1567,(0,0))),((4,1),(1568,(0,0))),((4,2),(1569,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_470_checked : successorFastRowCheck layer8 row7_470 row7_470choice = true := by decide
def row7_471 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def row7_471choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1793,(1,0))),((0,0),(446,(0,0))),((0,2),(1285,(0,0))),((1,-1),(2101,(0,1))),((1,3),(1507,(0,0))),((2,0),(1532,(0,0))),((2,1),(1546,(0,0))),((2,3),(1562,(0,0))),((3,1),(1567,(0,0))),((3,4),(1570,(0,0))),((4,2),(1571,(0,0))),((4,3),(1572,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_471_checked : successorFastRowCheck layer8 row7_471 row7_471choice = true := by decide
def Closure7C058rows : List (List GridPoint) := [row7_464,row7_465,row7_466,row7_467,row7_468,row7_469,row7_470,row7_471]
theorem Closure7C058_closed : ∀ row ∈ Closure7C058rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C058rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_464choice,row7_464_checked⟩
  · subst row
    exact ⟨row7_465choice,row7_465_checked⟩
  · subst row
    exact ⟨row7_466choice,row7_466_checked⟩
  · subst row
    exact ⟨row7_467choice,row7_467_checked⟩
  · subst row
    exact ⟨row7_468choice,row7_468_checked⟩
  · subst row
    exact ⟨row7_469choice,row7_469_checked⟩
  · subst row
    exact ⟨row7_470choice,row7_470_checked⟩
  · subst row
    exact ⟨row7_471choice,row7_471_checked⟩
end Polyomino57
