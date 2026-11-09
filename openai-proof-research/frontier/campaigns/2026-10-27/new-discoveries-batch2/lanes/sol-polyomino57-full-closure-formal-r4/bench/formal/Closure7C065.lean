import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_520 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)]
def row7_520choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1842,(1,0))),((0,0),(584,(0,0))),((0,2),(1339,(0,0))),((1,0),(1548,(0,0))),((1,3),(1696,(0,0))),((2,0),(1713,(0,0))),((2,2),(1726,(0,0))),((3,-1),(2284,(0,1))),((3,3),(1730,(0,0))),((4,0),(1731,(0,0))),((4,1),(1732,(0,0))),((4,2),(1733,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_520_checked : successorFastRowCheck layer8 row7_520 row7_520choice = true := by decide
def row7_521 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)]
def row7_521choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1843,(1,0))),((0,0),(585,(0,0))),((0,2),(1340,(0,0))),((1,0),(1549,(0,0))),((1,3),(1697,(0,0))),((2,0),(1714,(0,0))),((2,2),(1727,(0,0))),((3,-1),(2286,(0,1))),((3,2),(1731,(0,0))),((4,-1),(2288,(0,1))),((4,1),(1734,(0,0))),((5,0),(1735,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_521_checked : successorFastRowCheck layer8 row7_521 row7_521choice = true := by decide
def row7_522 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]
def row7_522choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1844,(1,0))),((0,0),(586,(0,0))),((0,2),(1341,(0,0))),((1,0),(1550,(0,0))),((1,3),(1698,(0,0))),((2,0),(1715,(0,0))),((2,2),(1728,(0,0))),((3,-1),(2287,(0,1))),((3,2),(1732,(0,0))),((4,0),(1734,(0,0))),((4,2),(1736,(0,0))),((5,1),(1737,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_522_checked : successorFastRowCheck layer8 row7_522 row7_522choice = true := by decide
def row7_523 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)]
def row7_523choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1845,(1,0))),((0,0),(590,(0,0))),((0,2),(1342,(0,0))),((1,0),(1554,(0,0))),((1,3),(1699,(0,0))),((2,0),(1721,(0,0))),((2,2),(1729,(0,0))),((3,0),(1734,(0,0))),((3,2),(1738,(0,0))),((4,-1),(2289,(0,1))),((4,2),(1739,(0,0))),((5,0),(1740,(0,0))),((5,1),(1741,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_523_checked : successorFastRowCheck layer8 row7_523 row7_523choice = true := by decide
def row7_524 : List GridPoint := [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)]
def row7_524choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1846,(1,0))),((0,0),(602,(0,0))),((0,2),(1343,(0,0))),((1,0),(1566,(0,0))),((1,3),(1700,(0,0))),((2,0),(1724,(0,0))),((2,1),(1726,(0,0))),((2,3),(1743,(0,0))),((3,-1),(2290,(0,1))),((3,3),(1744,(0,0))),((4,0),(1745,(0,0))),((4,1),(1746,(0,0))),((4,2),(1747,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_524_checked : successorFastRowCheck layer8 row7_524 row7_524choice = true := by decide
def row7_525 : List GridPoint := [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_525choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1847,(1,0))),((0,0),(613,(0,0))),((0,2),(1344,(0,0))),((0,3),(1449,(0,0))),((1,0),(1577,(0,0))),((1,2),(1682,(0,0))),((1,4),(1750,(0,0))),((2,-1),(2291,(0,1))),((2,4),(1751,(0,0))),((3,0),(1752,(0,0))),((3,1),(1753,(0,0))),((3,2),(1754,(0,0))),((3,3),(1755,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_525_checked : successorFastRowCheck layer8 row7_525 row7_525choice = true := by decide
def row7_526 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)]
def row7_526choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1848,(1,0))),((0,0),(619,(0,0))),((0,2),(1345,(0,0))),((1,0),(1583,(0,0))),((1,2),(1701,(0,0))),((1,3),(1751,(0,0))),((1,4),(1757,(0,0))),((2,-1),(2292,(0,1))),((2,5),(1758,(0,0))),((3,0),(1759,(0,0))),((3,1),(1760,(0,0))),((3,2),(1761,(0,0))),((3,3),(1762,(0,0))),((3,4),(1763,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_526_checked : successorFastRowCheck layer8 row7_526 row7_526choice = true := by decide
def row7_527 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)]
def row7_527choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1849,(1,0))),((0,0),(620,(0,0))),((0,2),(1346,(0,0))),((1,0),(1584,(0,0))),((1,2),(1702,(0,0))),((1,3),(1752,(0,0))),((2,-1),(2294,(0,1))),((2,4),(1759,(0,0))),((3,-1),(2334,(0,1))),((3,1),(1764,(0,0))),((3,2),(1765,(0,0))),((3,3),(1766,(0,0))),((4,0),(1767,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_527_checked : successorFastRowCheck layer8 row7_527 row7_527choice = true := by decide
def Closure7C065rows : List (List GridPoint) := [row7_520,row7_521,row7_522,row7_523,row7_524,row7_525,row7_526,row7_527]
theorem Closure7C065_closed : ∀ row ∈ Closure7C065rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C065rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_520choice,row7_520_checked⟩
  · subst row
    exact ⟨row7_521choice,row7_521_checked⟩
  · subst row
    exact ⟨row7_522choice,row7_522_checked⟩
  · subst row
    exact ⟨row7_523choice,row7_523_checked⟩
  · subst row
    exact ⟨row7_524choice,row7_524_checked⟩
  · subst row
    exact ⟨row7_525choice,row7_525_checked⟩
  · subst row
    exact ⟨row7_526choice,row7_526_checked⟩
  · subst row
    exact ⟨row7_527choice,row7_527_checked⟩
end Polyomino57
