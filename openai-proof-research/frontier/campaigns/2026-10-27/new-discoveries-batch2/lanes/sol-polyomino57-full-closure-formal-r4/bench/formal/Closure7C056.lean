import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_448 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def row7_448choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1770,(1,0))),((0,0),(423,(0,0))),((0,2),(1262,(0,0))),((0,3),(1437,(0,0))),((1,-1),(2065,(0,1))),((1,4),(1474,(0,0))),((2,0),(1485,(0,0))),((2,2),(1495,(0,0))),((2,3),(1498,(0,0))),((3,0),(1500,(0,0))),((3,2),(1501,(0,0))),((4,1),(1502,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_448_checked : successorFastRowCheck layer8 row7_448 row7_448choice = true := by decide
def row7_449 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def row7_449choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1771,(1,0))),((0,0),(424,(0,0))),((0,2),(1263,(0,0))),((0,3),(1438,(0,0))),((1,-1),(2066,(0,1))),((1,4),(1475,(0,0))),((2,0),(1486,(0,0))),((2,1),(1494,(0,0))),((2,4),(1503,(0,0))),((3,2),(1504,(0,0))),((3,3),(1505,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_449_checked : successorFastRowCheck layer8 row7_449 row7_449choice = true := by decide
def row7_450 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def row7_450choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1772,(1,0))),((0,0),(425,(0,0))),((0,2),(1264,(0,0))),((0,3),(1439,(0,0))),((1,-1),(2067,(0,1))),((1,4),(1477,(0,0))),((2,0),(1488,(0,0))),((2,1),(1496,(0,0))),((2,3),(1504,(0,0))),((3,1),(1506,(0,0))),((3,3),(1507,(0,0))),((4,2),(1508,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_450_checked : successorFastRowCheck layer8 row7_450 row7_450choice = true := by decide
def row7_451 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def row7_451choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1773,(1,0))),((0,0),(426,(0,0))),((0,2),(1265,(0,0))),((0,3),(1440,(0,0))),((1,-1),(2068,(0,1))),((1,4),(1478,(0,0))),((2,0),(1489,(0,0))),((2,1),(1497,(0,0))),((2,2),(1503,(0,0))),((2,5),(1509,(0,0))),((3,3),(1510,(0,0))),((3,4),(1511,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_451_checked : successorFastRowCheck layer8 row7_451 row7_451choice = true := by decide
def row7_452 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def row7_452choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1774,(1,0))),((0,0),(427,(0,0))),((0,2),(1266,(0,0))),((0,3),(1441,(0,0))),((1,-1),(2069,(0,1))),((1,4),(1479,(0,0))),((2,0),(1491,(0,0))),((2,1),(1499,(0,0))),((2,2),(1505,(0,0))),((2,4),(1510,(0,0))),((3,2),(1512,(0,0))),((3,4),(1513,(0,0))),((4,3),(1514,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_452_checked : successorFastRowCheck layer8 row7_452 row7_452choice = true := by decide
def row7_453 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_453choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1775,(1,0))),((0,0),(428,(0,0))),((0,2),(1267,(0,0))),((1,-1),(2082,(0,1))),((1,3),(1482,(0,0))),((2,-1),(2189,(0,1))),((2,3),(1516,(0,0))),((3,0),(1517,(0,0))),((3,1),(1518,(0,0))),((3,2),(1519,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_453_checked : successorFastRowCheck layer8 row7_453 row7_453choice = true := by decide
def row7_454 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_454choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1776,(1,0))),((0,0),(429,(0,0))),((0,2),(1268,(0,0))),((1,-1),(2083,(0,1))),((1,3),(1484,(0,0))),((2,-1),(2191,(0,1))),((2,2),(1517,(0,0))),((3,-1),(2201,(0,1))),((3,1),(1520,(0,0))),((4,0),(1521,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_454_checked : successorFastRowCheck layer8 row7_454 row7_454choice = true := by decide
def row7_455 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_455choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1777,(1,0))),((0,0),(430,(0,0))),((0,2),(1269,(0,0))),((1,-1),(2084,(0,1))),((1,3),(1485,(0,0))),((2,-1),(2192,(0,1))),((2,2),(1518,(0,0))),((3,0),(1520,(0,0))),((3,2),(1522,(0,0))),((4,1),(1523,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_455_checked : successorFastRowCheck layer8 row7_455 row7_455choice = true := by decide
def Closure7C056rows : List (List GridPoint) := [row7_448,row7_449,row7_450,row7_451,row7_452,row7_453,row7_454,row7_455]
theorem Closure7C056_closed : ∀ row ∈ Closure7C056rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C056rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_448choice,row7_448_checked⟩
  · subst row
    exact ⟨row7_449choice,row7_449_checked⟩
  · subst row
    exact ⟨row7_450choice,row7_450_checked⟩
  · subst row
    exact ⟨row7_451choice,row7_451_checked⟩
  · subst row
    exact ⟨row7_452choice,row7_452_checked⟩
  · subst row
    exact ⟨row7_453choice,row7_453_checked⟩
  · subst row
    exact ⟨row7_454choice,row7_454_checked⟩
  · subst row
    exact ⟨row7_455choice,row7_455_checked⟩
end Polyomino57
