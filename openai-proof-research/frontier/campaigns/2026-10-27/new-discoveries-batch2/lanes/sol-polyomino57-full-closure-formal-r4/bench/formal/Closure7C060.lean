import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_480 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)]
def row7_480choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1802,(1,0))),((0,0),(455,(0,0))),((0,2),(1294,(0,0))),((1,-1),(2134,(0,1))),((1,2),(1522,(0,0))),((2,-1),(2218,(0,1))),((2,2),(1591,(0,0))),((3,0),(1595,(0,0))),((3,3),(1600,(0,0))),((4,1),(1601,(0,0))),((4,2),(1602,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_480_checked : successorFastRowCheck layer8 row7_480 row7_480choice = true := by decide
def row7_481 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]
def row7_481choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1803,(1,0))),((0,0),(456,(0,0))),((0,2),(1295,(0,0))),((1,-1),(2135,(0,1))),((1,2),(1523,(0,0))),((2,-1),(2219,(0,1))),((2,2),(1592,(0,0))),((3,0),(1597,(0,0))),((3,2),(1601,(0,0))),((4,0),(1603,(0,0))),((4,2),(1604,(0,0))),((5,1),(1605,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_481_checked : successorFastRowCheck layer8 row7_481 row7_481choice = true := by decide
def row7_482 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)]
def row7_482choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1804,(1,0))),((0,0),(457,(0,0))),((0,2),(1296,(0,0))),((1,-1),(2139,(0,1))),((1,2),(1534,(0,0))),((2,-1),(2225,(0,1))),((2,1),(1595,(0,0))),((2,2),(1606,(0,0))),((3,-1),(2237,(0,1))),((3,3),(1607,(0,0))),((4,0),(1608,(0,0))),((4,1),(1609,(0,0))),((4,2),(1610,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_482_checked : successorFastRowCheck layer8 row7_482 row7_482choice = true := by decide
def row7_483 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)]
def row7_483choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1805,(1,0))),((0,0),(458,(0,0))),((0,2),(1297,(0,0))),((1,-1),(2140,(0,1))),((1,2),(1535,(0,0))),((2,-1),(2226,(0,1))),((2,1),(1596,(0,0))),((3,-1),(2239,(0,1))),((3,2),(1608,(0,0))),((4,-1),(2245,(0,1))),((4,1),(1611,(0,0))),((5,0),(1612,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_483_checked : successorFastRowCheck layer8 row7_483 row7_483choice = true := by decide
def row7_484 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]
def row7_484choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1806,(1,0))),((0,0),(459,(0,0))),((0,2),(1298,(0,0))),((1,-1),(2141,(0,1))),((1,2),(1536,(0,0))),((2,-1),(2227,(0,1))),((2,1),(1597,(0,0))),((3,-1),(2240,(0,1))),((3,2),(1609,(0,0))),((4,0),(1611,(0,0))),((4,2),(1613,(0,0))),((5,1),(1614,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_484_checked : successorFastRowCheck layer8 row7_484 row7_484choice = true := by decide
def row7_485 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)]
def row7_485choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1807,(1,0))),((0,0),(460,(0,0))),((0,2),(1299,(0,0))),((1,-1),(2143,(0,1))),((1,2),(1537,(0,0))),((2,-1),(2229,(0,1))),((2,1),(1598,(0,0))),((3,-1),(2243,(0,1))),((3,1),(1611,(0,0))),((4,-1),(2246,(0,1))),((4,2),(1615,(0,0))),((5,0),(1616,(0,0))),((5,1),(1617,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_485_checked : successorFastRowCheck layer8 row7_485 row7_485choice = true := by decide
def row7_486 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]
def row7_486choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1808,(1,0))),((0,0),(461,(0,0))),((0,2),(1300,(0,0))),((1,-1),(2144,(0,1))),((1,2),(1538,(0,0))),((2,-1),(2230,(0,1))),((2,1),(1599,(0,0))),((3,-1),(2244,(0,1))),((3,1),(1612,(0,0))),((4,-1),(2248,(0,1))),((4,1),(1616,(0,0))),((5,-1),(2249,(0,1))),((5,1),(1618,(0,0))),((6,0),(1619,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_486_checked : successorFastRowCheck layer8 row7_486 row7_486choice = true := by decide
def row7_487 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)]
def row7_487choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1809,(1,0))),((0,0),(462,(0,0))),((0,2),(1301,(0,0))),((1,-1),(2145,(0,1))),((1,2),(1539,(0,0))),((1,3),(1578,(0,0))),((1,4),(1582,(0,0))),((2,0),(1583,(0,0))),((2,5),(1620,(0,0))),((3,1),(1621,(0,0))),((3,2),(1622,(0,0))),((3,3),(1623,(0,0))),((3,4),(1624,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_487_checked : successorFastRowCheck layer8 row7_487 row7_487choice = true := by decide
def Closure7C060rows : List (List GridPoint) := [row7_480,row7_481,row7_482,row7_483,row7_484,row7_485,row7_486,row7_487]
theorem Closure7C060_closed : ∀ row ∈ Closure7C060rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C060rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_480choice,row7_480_checked⟩
  · subst row
    exact ⟨row7_481choice,row7_481_checked⟩
  · subst row
    exact ⟨row7_482choice,row7_482_checked⟩
  · subst row
    exact ⟨row7_483choice,row7_483_checked⟩
  · subst row
    exact ⟨row7_484choice,row7_484_checked⟩
  · subst row
    exact ⟨row7_485choice,row7_485_checked⟩
  · subst row
    exact ⟨row7_486choice,row7_486_checked⟩
  · subst row
    exact ⟨row7_487choice,row7_487_checked⟩
end Polyomino57
