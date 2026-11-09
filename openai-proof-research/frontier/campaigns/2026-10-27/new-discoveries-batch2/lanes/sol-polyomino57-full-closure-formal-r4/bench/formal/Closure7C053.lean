import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_424 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_424choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1746,(1,0))),((-1,2),(2253,(1,0))),((0,0),(348,(0,0))),((0,3),(1244,(0,0))),((1,0),(1322,(0,0))),((1,1),(1332,(0,0))),((1,3),(1389,(0,0))),((2,-1),(2032,(0,1))),((2,3),(1395,(0,0))),((3,0),(1398,(0,0))),((3,2),(1401,(0,0))),((4,1),(1402,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_424_checked : successorFastRowCheck layer8 row7_424 row7_424choice = true := by decide
def row7_425 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_425choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1747,(1,0))),((-1,2),(2254,(1,0))),((0,0),(349,(0,0))),((0,3),(1245,(0,0))),((1,0),(1323,(0,0))),((1,1),(1333,(0,0))),((1,3),(1390,(0,0))),((2,-1),(2033,(0,1))),((2,3),(1396,(0,0))),((3,0),(1399,(0,0))),((3,1),(1401,(0,0))),((3,3),(1403,(0,0))),((4,2),(1404,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_425_checked : successorFastRowCheck layer8 row7_425 row7_425choice = true := by decide
def row7_426 : List GridPoint := [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)]
def row7_426choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1748,(1,0))),((-1,2),(2255,(1,0))),((0,0),(354,(0,0))),((0,3),(1246,(0,0))),((1,1),(1338,(0,0))),((1,3),(1391,(0,0))),((2,0),(1398,(0,0))),((2,3),(1406,(0,0))),((3,-1),(2035,(0,1))),((3,2),(1407,(0,0))),((4,0),(1408,(0,0))),((4,1),(1409,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_426_checked : successorFastRowCheck layer8 row7_426 row7_426choice = true := by decide
def row7_427 : List GridPoint := [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)]
def row7_427choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1749,(1,0))),((-1,2),(2256,(1,0))),((0,0),(368,(0,0))),((0,3),(1247,(0,0))),((1,1),(1343,(0,0))),((1,3),(1392,(0,0))),((2,0),(1405,(0,0))),((2,1),(1407,(0,0))),((2,3),(1411,(0,0))),((3,-1),(2036,(0,1))),((3,3),(1412,(0,0))),((4,0),(1413,(0,0))),((4,1),(1414,(0,0))),((4,2),(1415,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_427_checked : successorFastRowCheck layer8 row7_427 row7_427choice = true := by decide
def row7_428 : List GridPoint := [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def row7_428choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1750,(1,0))),((-1,3),(2540,(1,0))),((-1,4),(2680,(1,0))),((0,0),(379,(0,0))),((0,2),(1154,(0,0))),((0,5),(1418,(0,0))),((1,-1),(2037,(0,1))),((1,4),(1419,(0,0))),((2,0),(1420,(0,0))),((2,1),(1421,(0,0))),((2,2),(1422,(0,0))),((2,3),(1423,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_428_checked : successorFastRowCheck layer8 row7_428 row7_428choice = true := by decide
def row7_429 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_429choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1751,(1,0))),((-1,3),(2541,(1,0))),((0,0),(384,(0,0))),((0,2),(1179,(0,0))),((0,4),(1419,(0,0))),((1,-1),(2038,(0,1))),((1,5),(1425,(0,0))),((2,0),(1426,(0,0))),((2,1),(1427,(0,0))),((2,2),(1428,(0,0))),((2,3),(1429,(0,0))),((2,4),(1430,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_429_checked : successorFastRowCheck layer8 row7_429 row7_429choice = true := by decide
def row7_430 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_430choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1752,(1,0))),((-1,3),(2542,(1,0))),((0,0),(385,(0,0))),((0,2),(1180,(0,0))),((0,4),(1420,(0,0))),((1,-1),(2040,(0,1))),((1,4),(1426,(0,0))),((2,-1),(2044,(0,1))),((2,1),(1431,(0,0))),((2,2),(1432,(0,0))),((2,3),(1433,(0,0))),((3,0),(1434,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_430_checked : successorFastRowCheck layer8 row7_430 row7_430choice = true := by decide
def row7_431 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_431choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1753,(1,0))),((-1,3),(2543,(1,0))),((0,0),(386,(0,0))),((0,2),(1181,(0,0))),((0,4),(1421,(0,0))),((1,-1),(2041,(0,1))),((1,4),(1427,(0,0))),((2,0),(1431,(0,0))),((2,2),(1435,(0,0))),((2,3),(1436,(0,0))),((3,1),(1437,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_431_checked : successorFastRowCheck layer8 row7_431 row7_431choice = true := by decide
def Closure7C053rows : List (List GridPoint) := [row7_424,row7_425,row7_426,row7_427,row7_428,row7_429,row7_430,row7_431]
theorem Closure7C053_closed : ∀ row ∈ Closure7C053rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C053rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_424choice,row7_424_checked⟩
  · subst row
    exact ⟨row7_425choice,row7_425_checked⟩
  · subst row
    exact ⟨row7_426choice,row7_426_checked⟩
  · subst row
    exact ⟨row7_427choice,row7_427_checked⟩
  · subst row
    exact ⟨row7_428choice,row7_428_checked⟩
  · subst row
    exact ⟨row7_429choice,row7_429_checked⟩
  · subst row
    exact ⟨row7_430choice,row7_430_checked⟩
  · subst row
    exact ⟨row7_431choice,row7_431_checked⟩
end Polyomino57
