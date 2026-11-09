import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_528 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)]
def row7_528choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1850,(1,0))),((0,0),(621,(0,0))),((0,2),(1347,(0,0))),((1,0),(1585,(0,0))),((1,2),(1703,(0,0))),((1,3),(1753,(0,0))),((2,-1),(2295,(0,1))),((2,4),(1760,(0,0))),((3,0),(1764,(0,0))),((3,2),(1768,(0,0))),((3,3),(1769,(0,0))),((4,1),(1770,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_528_checked : successorFastRowCheck layer8 row7_528 row7_528choice = true := by decide
def row7_529 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)]
def row7_529choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1851,(1,0))),((0,0),(622,(0,0))),((0,2),(1348,(0,0))),((1,0),(1586,(0,0))),((1,2),(1704,(0,0))),((1,3),(1754,(0,0))),((2,-1),(2296,(0,1))),((2,4),(1761,(0,0))),((3,0),(1765,(0,0))),((3,1),(1768,(0,0))),((3,3),(1771,(0,0))),((4,2),(1772,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_529_checked : successorFastRowCheck layer8 row7_529 row7_529choice = true := by decide
def row7_530 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]
def row7_530choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1852,(1,0))),((0,0),(623,(0,0))),((0,2),(1349,(0,0))),((1,0),(1587,(0,0))),((1,2),(1705,(0,0))),((1,3),(1755,(0,0))),((2,-1),(2297,(0,1))),((2,4),(1762,(0,0))),((3,0),(1766,(0,0))),((3,1),(1769,(0,0))),((3,2),(1771,(0,0))),((3,4),(1773,(0,0))),((4,3),(1774,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_530_checked : successorFastRowCheck layer8 row7_530 row7_530choice = true := by decide
def row7_531 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)]
def row7_531choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1853,(1,0))),((0,0),(624,(0,0))),((0,2),(1350,(0,0))),((1,0),(1588,(0,0))),((1,2),(1706,(0,0))),((2,-1),(2302,(0,1))),((2,3),(1764,(0,0))),((3,-1),(2335,(0,1))),((3,2),(1775,(0,0))),((4,0),(1776,(0,0))),((4,1),(1777,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_531_checked : successorFastRowCheck layer8 row7_531 row7_531choice = true := by decide
def row7_532 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)]
def row7_532choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1854,(1,0))),((0,0),(625,(0,0))),((0,2),(1351,(0,0))),((1,0),(1589,(0,0))),((1,2),(1707,(0,0))),((2,-1),(2303,(0,1))),((2,3),(1765,(0,0))),((3,-1),(2336,(0,1))),((3,1),(1775,(0,0))),((3,3),(1778,(0,0))),((4,0),(1779,(0,0))),((4,2),(1780,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_532_checked : successorFastRowCheck layer8 row7_532 row7_532choice = true := by decide
def row7_533 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]
def row7_533choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1855,(1,0))),((0,0),(626,(0,0))),((0,2),(1352,(0,0))),((1,0),(1590,(0,0))),((1,2),(1708,(0,0))),((2,-1),(2304,(0,1))),((2,3),(1767,(0,0))),((3,-1),(2338,(0,1))),((3,1),(1776,(0,0))),((3,2),(1779,(0,0))),((4,-1),(2339,(0,1))),((4,1),(1781,(0,0))),((5,0),(1782,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_533_checked : successorFastRowCheck layer8 row7_533 row7_533choice = true := by decide
def row7_534 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)]
def row7_534choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1856,(1,0))),((0,0),(627,(0,0))),((0,2),(1353,(0,0))),((1,0),(1591,(0,0))),((1,2),(1709,(0,0))),((2,-1),(2305,(0,1))),((2,3),(1768,(0,0))),((3,0),(1775,(0,0))),((3,3),(1783,(0,0))),((4,1),(1784,(0,0))),((4,2),(1785,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_534_checked : successorFastRowCheck layer8 row7_534 row7_534choice = true := by decide
def row7_535 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]
def row7_535choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1857,(1,0))),((0,0),(628,(0,0))),((0,2),(1354,(0,0))),((1,0),(1592,(0,0))),((1,2),(1710,(0,0))),((2,-1),(2306,(0,1))),((2,3),(1770,(0,0))),((3,0),(1777,(0,0))),((3,2),(1784,(0,0))),((4,0),(1786,(0,0))),((4,2),(1787,(0,0))),((5,1),(1788,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_535_checked : successorFastRowCheck layer8 row7_535 row7_535choice = true := by decide
def Closure7C066rows : List (List GridPoint) := [row7_528,row7_529,row7_530,row7_531,row7_532,row7_533,row7_534,row7_535]
theorem Closure7C066_closed : ∀ row ∈ Closure7C066rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C066rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_528choice,row7_528_checked⟩
  · subst row
    exact ⟨row7_529choice,row7_529_checked⟩
  · subst row
    exact ⟨row7_530choice,row7_530_checked⟩
  · subst row
    exact ⟨row7_531choice,row7_531_checked⟩
  · subst row
    exact ⟨row7_532choice,row7_532_checked⟩
  · subst row
    exact ⟨row7_533choice,row7_533_checked⟩
  · subst row
    exact ⟨row7_534choice,row7_534_checked⟩
  · subst row
    exact ⟨row7_535choice,row7_535_checked⟩
end Polyomino57
