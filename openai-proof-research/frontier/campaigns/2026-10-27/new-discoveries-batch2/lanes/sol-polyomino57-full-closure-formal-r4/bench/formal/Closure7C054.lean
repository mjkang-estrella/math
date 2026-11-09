import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_432 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_432choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1754,(1,0))),((-1,3),(2544,(1,0))),((0,0),(387,(0,0))),((0,2),(1182,(0,0))),((0,4),(1422,(0,0))),((1,-1),(2042,(0,1))),((1,4),(1428,(0,0))),((2,0),(1432,(0,0))),((2,1),(1435,(0,0))),((2,3),(1438,(0,0))),((3,2),(1439,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_432_checked : successorFastRowCheck layer8 row7_432 row7_432choice = true := by decide
def row7_433 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_433choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1755,(1,0))),((-1,3),(2545,(1,0))),((0,0),(388,(0,0))),((0,2),(1183,(0,0))),((0,4),(1423,(0,0))),((1,-1),(2043,(0,1))),((1,4),(1429,(0,0))),((2,0),(1433,(0,0))),((2,1),(1436,(0,0))),((2,2),(1438,(0,0))),((2,4),(1440,(0,0))),((3,3),(1441,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_433_checked : successorFastRowCheck layer8 row7_433 row7_433choice = true := by decide
def row7_434 : List GridPoint := [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_434choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1756,(1,0))),((-1,3),(2546,(1,0))),((0,0),(394,(0,0))),((0,2),(1217,(0,0))),((0,4),(1424,(0,0))),((1,0),(1431,(0,0))),((1,4),(1443,(0,0))),((2,-1),(2045,(0,1))),((2,2),(1444,(0,0))),((2,3),(1445,(0,0))),((3,0),(1446,(0,0))),((3,1),(1447,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_434_checked : successorFastRowCheck layer8 row7_434 row7_434choice = true := by decide
def row7_435 : List GridPoint := [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_435choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1757,(1,0))),((-1,4),(2681,(1,0))),((0,0),(404,(0,0))),((0,2),(1249,(0,0))),((0,3),(1419,(0,0))),((0,5),(1450,(0,0))),((1,-1),(2046,(0,1))),((1,5),(1451,(0,0))),((2,0),(1452,(0,0))),((2,1),(1453,(0,0))),((2,2),(1454,(0,0))),((2,3),(1455,(0,0))),((2,4),(1456,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_435_checked : successorFastRowCheck layer8 row7_435 row7_435choice = true := by decide
def row7_436 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_436choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1758,(1,0))),((0,0),(411,(0,0))),((0,2),(1250,(0,0))),((0,3),(1425,(0,0))),((0,4),(1451,(0,0))),((0,5),(1458,(0,0))),((1,-1),(2047,(0,1))),((1,6),(1459,(0,0))),((2,0),(1460,(0,0))),((2,1),(1461,(0,0))),((2,2),(1462,(0,0))),((2,3),(1463,(0,0))),((2,4),(1464,(0,0))),((2,5),(1465,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_436_checked : successorFastRowCheck layer8 row7_436 row7_436choice = true := by decide
def row7_437 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def row7_437choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1759,(1,0))),((0,0),(412,(0,0))),((0,2),(1251,(0,0))),((0,3),(1426,(0,0))),((0,4),(1452,(0,0))),((1,-1),(2049,(0,1))),((1,5),(1460,(0,0))),((2,-1),(2182,(0,1))),((2,1),(1466,(0,0))),((2,2),(1467,(0,0))),((2,3),(1468,(0,0))),((2,4),(1469,(0,0))),((3,0),(1470,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_437_checked : successorFastRowCheck layer8 row7_437 row7_437choice = true := by decide
def row7_438 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_438choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1760,(1,0))),((0,0),(413,(0,0))),((0,2),(1252,(0,0))),((0,3),(1427,(0,0))),((0,4),(1453,(0,0))),((1,-1),(2050,(0,1))),((1,5),(1461,(0,0))),((2,0),(1466,(0,0))),((2,2),(1471,(0,0))),((2,3),(1472,(0,0))),((2,4),(1473,(0,0))),((3,1),(1474,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_438_checked : successorFastRowCheck layer8 row7_438 row7_438choice = true := by decide
def row7_439 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_439choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1761,(1,0))),((0,0),(414,(0,0))),((0,2),(1253,(0,0))),((0,3),(1428,(0,0))),((0,4),(1454,(0,0))),((1,-1),(2051,(0,1))),((1,5),(1462,(0,0))),((2,0),(1467,(0,0))),((2,1),(1471,(0,0))),((2,3),(1475,(0,0))),((2,4),(1476,(0,0))),((3,2),(1477,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_439_checked : successorFastRowCheck layer8 row7_439 row7_439choice = true := by decide
def Closure7C054rows : List (List GridPoint) := [row7_432,row7_433,row7_434,row7_435,row7_436,row7_437,row7_438,row7_439]
theorem Closure7C054_closed : ∀ row ∈ Closure7C054rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C054rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_432choice,row7_432_checked⟩
  · subst row
    exact ⟨row7_433choice,row7_433_checked⟩
  · subst row
    exact ⟨row7_434choice,row7_434_checked⟩
  · subst row
    exact ⟨row7_435choice,row7_435_checked⟩
  · subst row
    exact ⟨row7_436choice,row7_436_checked⟩
  · subst row
    exact ⟨row7_437choice,row7_437_checked⟩
  · subst row
    exact ⟨row7_438choice,row7_438_checked⟩
  · subst row
    exact ⟨row7_439choice,row7_439_checked⟩
end Polyomino57
