import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_496 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)]
def row7_496choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1818,(1,0))),((0,0),(471,(0,0))),((0,2),(1310,(0,0))),((1,-1),(2155,(0,1))),((1,2),(1548,(0,0))),((2,0),(1595,(0,0))),((2,2),(1633,(0,0))),((3,-1),(2251,(0,1))),((3,3),(1649,(0,0))),((4,0),(1650,(0,0))),((4,1),(1651,(0,0))),((4,2),(1652,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_496_checked : successorFastRowCheck layer8 row7_496 row7_496choice = true := by decide
def row7_497 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)]
def row7_497choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1819,(1,0))),((0,0),(472,(0,0))),((0,2),(1311,(0,0))),((1,-1),(2156,(0,1))),((1,2),(1549,(0,0))),((2,0),(1596,(0,0))),((2,2),(1634,(0,0))),((3,-1),(2253,(0,1))),((3,2),(1650,(0,0))),((4,-1),(2255,(0,1))),((4,1),(1653,(0,0))),((5,0),(1654,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_497_checked : successorFastRowCheck layer8 row7_497 row7_497choice = true := by decide
def row7_498 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]
def row7_498choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1820,(1,0))),((0,0),(473,(0,0))),((0,2),(1312,(0,0))),((1,-1),(2157,(0,1))),((1,2),(1550,(0,0))),((2,0),(1597,(0,0))),((2,2),(1635,(0,0))),((3,-1),(2254,(0,1))),((3,2),(1651,(0,0))),((4,0),(1653,(0,0))),((4,2),(1655,(0,0))),((5,1),(1656,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_498_checked : successorFastRowCheck layer8 row7_498 row7_498choice = true := by decide
def row7_499 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)]
def row7_499choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1821,(1,0))),((0,0),(474,(0,0))),((0,2),(1313,(0,0))),((1,-1),(2158,(0,1))),((1,2),(1551,(0,0))),((2,0),(1600,(0,0))),((2,2),(1636,(0,0))),((2,3),(1648,(0,0))),((3,0),(1649,(0,0))),((3,4),(1657,(0,0))),((4,1),(1658,(0,0))),((4,2),(1659,(0,0))),((4,3),(1660,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_499_checked : successorFastRowCheck layer8 row7_499 row7_499choice = true := by decide
def row7_500 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)]
def row7_500choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1822,(1,0))),((0,0),(475,(0,0))),((0,2),(1314,(0,0))),((1,-1),(2159,(0,1))),((1,2),(1552,(0,0))),((2,0),(1601,(0,0))),((2,2),(1637,(0,0))),((3,0),(1651,(0,0))),((3,3),(1658,(0,0))),((4,0),(1661,(0,0))),((4,2),(1662,(0,0))),((5,1),(1663,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_500_checked : successorFastRowCheck layer8 row7_500 row7_500choice = true := by decide
def row7_501 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]
def row7_501choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1823,(1,0))),((0,0),(476,(0,0))),((0,2),(1315,(0,0))),((1,-1),(2160,(0,1))),((1,2),(1553,(0,0))),((2,0),(1602,(0,0))),((2,2),(1638,(0,0))),((3,0),(1652,(0,0))),((3,3),(1659,(0,0))),((4,1),(1662,(0,0))),((4,3),(1664,(0,0))),((5,2),(1665,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_501_checked : successorFastRowCheck layer8 row7_501 row7_501choice = true := by decide
def row7_502 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)]
def row7_502choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1824,(1,0))),((0,0),(477,(0,0))),((0,2),(1316,(0,0))),((1,-1),(2161,(0,1))),((1,2),(1554,(0,0))),((2,0),(1603,(0,0))),((2,2),(1639,(0,0))),((3,0),(1653,(0,0))),((3,2),(1661,(0,0))),((4,-1),(2256,(0,1))),((4,2),(1666,(0,0))),((5,0),(1667,(0,0))),((5,1),(1668,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_502_checked : successorFastRowCheck layer8 row7_502 row7_502choice = true := by decide
def row7_503 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)]
def row7_503choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1825,(1,0))),((0,0),(478,(0,0))),((0,2),(1317,(0,0))),((1,-1),(2162,(0,1))),((1,2),(1555,(0,0))),((2,0),(1604,(0,0))),((2,2),(1640,(0,0))),((3,0),(1655,(0,0))),((3,2),(1662,(0,0))),((4,0),(1666,(0,0))),((4,3),(1669,(0,0))),((5,1),(1670,(0,0))),((5,2),(1671,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_503_checked : successorFastRowCheck layer8 row7_503 row7_503choice = true := by decide
def Closure7C062rows : List (List GridPoint) := [row7_496,row7_497,row7_498,row7_499,row7_500,row7_501,row7_502,row7_503]
theorem Closure7C062_closed : ∀ row ∈ Closure7C062rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C062rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_496choice,row7_496_checked⟩
  · subst row
    exact ⟨row7_497choice,row7_497_checked⟩
  · subst row
    exact ⟨row7_498choice,row7_498_checked⟩
  · subst row
    exact ⟨row7_499choice,row7_499_checked⟩
  · subst row
    exact ⟨row7_500choice,row7_500_checked⟩
  · subst row
    exact ⟨row7_501choice,row7_501_checked⟩
  · subst row
    exact ⟨row7_502choice,row7_502_checked⟩
  · subst row
    exact ⟨row7_503choice,row7_503_checked⟩
end Polyomino57
