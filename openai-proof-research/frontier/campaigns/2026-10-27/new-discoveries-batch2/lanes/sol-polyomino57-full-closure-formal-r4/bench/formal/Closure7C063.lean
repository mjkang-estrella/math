import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_504 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]
def row7_504choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1826,(1,0))),((0,0),(479,(0,0))),((0,2),(1318,(0,0))),((1,-1),(2163,(0,1))),((1,2),(1556,(0,0))),((2,0),(1605,(0,0))),((2,2),(1641,(0,0))),((3,0),(1656,(0,0))),((3,2),(1663,(0,0))),((4,0),(1668,(0,0))),((4,2),(1670,(0,0))),((5,0),(1672,(0,0))),((5,2),(1673,(0,0))),((6,1),(1674,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_504_checked : successorFastRowCheck layer8 row7_504 row7_504choice = true := by decide
def row7_505 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def row7_505choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1827,(1,0))),((0,0),(529,(0,0))),((0,2),(1324,(0,0))),((0,3),(1443,(0,0))),((0,4),(1457,(0,0))),((1,0),(1466,(0,0))),((1,5),(1675,(0,0))),((2,-1),(2257,(0,1))),((2,2),(1676,(0,0))),((2,3),(1677,(0,0))),((2,4),(1678,(0,0))),((3,0),(1679,(0,0))),((3,1),(1680,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_505_checked : successorFastRowCheck layer8 row7_505 row7_505choice = true := by decide
def row7_506 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_506choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1828,(1,0))),((0,0),(541,(0,0))),((0,2),(1325,(0,0))),((0,3),(1444,(0,0))),((1,0),(1482,(0,0))),((1,4),(1676,(0,0))),((2,-1),(2258,(0,1))),((2,3),(1682,(0,0))),((3,0),(1683,(0,0))),((3,1),(1684,(0,0))),((3,2),(1685,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_506_checked : successorFastRowCheck layer8 row7_506 row7_506choice = true := by decide
def row7_507 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)]
def row7_507choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1829,(1,0))),((0,0),(542,(0,0))),((0,2),(1326,(0,0))),((0,3),(1445,(0,0))),((1,0),(1483,(0,0))),((1,4),(1677,(0,0))),((2,-1),(2259,(0,1))),((2,2),(1682,(0,0))),((2,4),(1686,(0,0))),((3,0),(1687,(0,0))),((3,1),(1688,(0,0))),((3,3),(1689,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_507_checked : successorFastRowCheck layer8 row7_507 row7_507choice = true := by decide
def row7_508 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]
def row7_508choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1830,(1,0))),((0,0),(543,(0,0))),((0,2),(1327,(0,0))),((0,3),(1446,(0,0))),((1,0),(1484,(0,0))),((1,4),(1679,(0,0))),((2,-1),(2261,(0,1))),((2,2),(1683,(0,0))),((2,3),(1687,(0,0))),((3,-1),(2263,(0,1))),((3,1),(1690,(0,0))),((4,0),(1691,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_508_checked : successorFastRowCheck layer8 row7_508 row7_508choice = true := by decide
def row7_509 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]
def row7_509choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1831,(1,0))),((0,0),(544,(0,0))),((0,2),(1328,(0,0))),((0,3),(1447,(0,0))),((1,0),(1485,(0,0))),((1,4),(1680,(0,0))),((2,-1),(2262,(0,1))),((2,2),(1684,(0,0))),((2,3),(1688,(0,0))),((3,0),(1690,(0,0))),((3,2),(1692,(0,0))),((4,1),(1693,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_509_checked : successorFastRowCheck layer8 row7_509 row7_509choice = true := by decide
def row7_510 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]
def row7_510choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1832,(1,0))),((0,0),(551,(0,0))),((0,2),(1329,(0,0))),((0,3),(1448,(0,0))),((1,0),(1500,(0,0))),((1,4),(1681,(0,0))),((2,0),(1690,(0,0))),((2,2),(1694,(0,0))),((2,3),(1695,(0,0))),((3,-1),(2264,(0,1))),((3,2),(1696,(0,0))),((4,0),(1697,(0,0))),((4,1),(1698,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_510_checked : successorFastRowCheck layer8 row7_510 row7_510choice = true := by decide
def row7_511 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_511choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1833,(1,0))),((0,0),(567,(0,0))),((0,2),(1330,(0,0))),((1,0),(1516,(0,0))),((1,3),(1682,(0,0))),((2,-1),(2265,(0,1))),((2,4),(1701,(0,0))),((3,0),(1702,(0,0))),((3,1),(1703,(0,0))),((3,2),(1704,(0,0))),((3,3),(1705,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_511_checked : successorFastRowCheck layer8 row7_511 row7_511choice = true := by decide
def Closure7C063rows : List (List GridPoint) := [row7_504,row7_505,row7_506,row7_507,row7_508,row7_509,row7_510,row7_511]
theorem Closure7C063_closed : ∀ row ∈ Closure7C063rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C063rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_504choice,row7_504_checked⟩
  · subst row
    exact ⟨row7_505choice,row7_505_checked⟩
  · subst row
    exact ⟨row7_506choice,row7_506_checked⟩
  · subst row
    exact ⟨row7_507choice,row7_507_checked⟩
  · subst row
    exact ⟨row7_508choice,row7_508_checked⟩
  · subst row
    exact ⟨row7_509choice,row7_509_checked⟩
  · subst row
    exact ⟨row7_510choice,row7_510_checked⟩
  · subst row
    exact ⟨row7_511choice,row7_511_checked⟩
end Polyomino57
