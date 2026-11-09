import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_440 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_440choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1762,(1,0))),((0,0),(415,(0,0))),((0,2),(1254,(0,0))),((0,3),(1429,(0,0))),((0,4),(1455,(0,0))),((1,-1),(2052,(0,1))),((1,5),(1463,(0,0))),((2,0),(1468,(0,0))),((2,1),(1472,(0,0))),((2,2),(1475,(0,0))),((2,4),(1478,(0,0))),((3,3),(1479,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_440_checked : successorFastRowCheck layer8 row7_440 row7_440choice = true := by decide
def row7_441 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_441choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1763,(1,0))),((0,0),(416,(0,0))),((0,2),(1255,(0,0))),((0,3),(1430,(0,0))),((0,4),(1456,(0,0))),((1,-1),(2053,(0,1))),((1,5),(1464,(0,0))),((2,0),(1469,(0,0))),((2,1),(1473,(0,0))),((2,2),(1476,(0,0))),((2,3),(1478,(0,0))),((2,5),(1480,(0,0))),((3,4),(1481,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_441_checked : successorFastRowCheck layer8 row7_441 row7_441choice = true := by decide
def row7_442 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_442choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1764,(1,0))),((0,0),(417,(0,0))),((0,2),(1256,(0,0))),((0,3),(1431,(0,0))),((1,-1),(2059,(0,1))),((1,4),(1466,(0,0))),((2,-1),(2183,(0,1))),((2,2),(1482,(0,0))),((2,3),(1483,(0,0))),((3,0),(1484,(0,0))),((3,1),(1485,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_442_checked : successorFastRowCheck layer8 row7_442 row7_442choice = true := by decide
def row7_443 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def row7_443choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1765,(1,0))),((0,0),(418,(0,0))),((0,2),(1257,(0,0))),((0,3),(1432,(0,0))),((1,-1),(2060,(0,1))),((1,4),(1467,(0,0))),((2,-1),(2184,(0,1))),((2,1),(1482,(0,0))),((2,3),(1486,(0,0))),((3,0),(1487,(0,0))),((3,2),(1488,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_443_checked : successorFastRowCheck layer8 row7_443 row7_443choice = true := by decide
def row7_444 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def row7_444choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1766,(1,0))),((0,0),(419,(0,0))),((0,2),(1258,(0,0))),((0,3),(1433,(0,0))),((1,-1),(2061,(0,1))),((1,4),(1468,(0,0))),((2,-1),(2185,(0,1))),((2,1),(1483,(0,0))),((2,2),(1486,(0,0))),((2,4),(1489,(0,0))),((3,0),(1490,(0,0))),((3,3),(1491,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_444_checked : successorFastRowCheck layer8 row7_444 row7_444choice = true := by decide
def row7_445 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def row7_445choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1767,(1,0))),((0,0),(420,(0,0))),((0,2),(1259,(0,0))),((0,3),(1434,(0,0))),((1,-1),(2062,(0,1))),((1,4),(1470,(0,0))),((2,-1),(2187,(0,1))),((2,1),(1484,(0,0))),((2,2),(1487,(0,0))),((2,3),(1490,(0,0))),((3,-1),(2188,(0,1))),((3,1),(1492,(0,0))),((4,0),(1493,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_445_checked : successorFastRowCheck layer8 row7_445 row7_445choice = true := by decide
def row7_446 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def row7_446choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1768,(1,0))),((0,0),(421,(0,0))),((0,2),(1260,(0,0))),((0,3),(1435,(0,0))),((1,-1),(2063,(0,1))),((1,4),(1471,(0,0))),((2,0),(1482,(0,0))),((2,3),(1494,(0,0))),((3,1),(1495,(0,0))),((3,2),(1496,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_446_checked : successorFastRowCheck layer8 row7_446 row7_446choice = true := by decide
def row7_447 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def row7_447choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1769,(1,0))),((0,0),(422,(0,0))),((0,2),(1261,(0,0))),((0,3),(1436,(0,0))),((1,-1),(2064,(0,1))),((1,4),(1472,(0,0))),((2,0),(1483,(0,0))),((2,2),(1494,(0,0))),((2,4),(1497,(0,0))),((3,1),(1498,(0,0))),((3,3),(1499,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_447_checked : successorFastRowCheck layer8 row7_447 row7_447choice = true := by decide
def Closure7C055rows : List (List GridPoint) := [row7_440,row7_441,row7_442,row7_443,row7_444,row7_445,row7_446,row7_447]
theorem Closure7C055_closed : ∀ row ∈ Closure7C055rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C055rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_440choice,row7_440_checked⟩
  · subst row
    exact ⟨row7_441choice,row7_441_checked⟩
  · subst row
    exact ⟨row7_442choice,row7_442_checked⟩
  · subst row
    exact ⟨row7_443choice,row7_443_checked⟩
  · subst row
    exact ⟨row7_444choice,row7_444_checked⟩
  · subst row
    exact ⟨row7_445choice,row7_445_checked⟩
  · subst row
    exact ⟨row7_446choice,row7_446_checked⟩
  · subst row
    exact ⟨row7_447choice,row7_447_checked⟩
end Polyomino57
