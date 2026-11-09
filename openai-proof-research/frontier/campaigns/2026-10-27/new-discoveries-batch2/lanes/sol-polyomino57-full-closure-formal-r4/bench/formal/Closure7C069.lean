import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_552 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]
def row7_552choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1874,(1,0))),((0,0),(657,(0,0))),((0,2),(1371,(0,0))),((1,0),(1635,(0,0))),((1,2),(1728,(0,0))),((2,0),(1777,(0,0))),((2,3),(1831,(0,0))),((3,-1),(2358,(0,1))),((3,2),(1835,(0,0))),((4,0),(1837,(0,0))),((4,2),(1839,(0,0))),((5,1),(1840,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_552_checked : successorFastRowCheck layer8 row7_552 row7_552choice = true := by decide
def row7_553 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)]
def row7_553choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1875,(1,0))),((0,0),(661,(0,0))),((0,2),(1372,(0,0))),((1,0),(1639,(0,0))),((1,2),(1729,(0,0))),((2,0),(1786,(0,0))),((2,3),(1832,(0,0))),((3,0),(1837,(0,0))),((3,2),(1841,(0,0))),((4,-1),(2360,(0,1))),((4,2),(1842,(0,0))),((5,0),(1843,(0,0))),((5,1),(1844,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_553_checked : successorFastRowCheck layer8 row7_553 row7_553choice = true := by decide
def row7_554 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)]
def row7_554choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1876,(1,0))),((0,0),(671,(0,0))),((0,2),(1373,(0,0))),((1,0),(1649,(0,0))),((1,2),(1730,(0,0))),((2,0),(1796,(0,0))),((2,2),(1833,(0,0))),((2,3),(1847,(0,0))),((3,-1),(2361,(0,1))),((3,4),(1848,(0,0))),((4,0),(1849,(0,0))),((4,1),(1850,(0,0))),((4,2),(1851,(0,0))),((4,3),(1852,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_554_checked : successorFastRowCheck layer8 row7_554 row7_554choice = true := by decide
def row7_555 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)]
def row7_555choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1877,(1,0))),((0,0),(672,(0,0))),((0,2),(1374,(0,0))),((1,0),(1650,(0,0))),((1,2),(1731,(0,0))),((2,0),(1797,(0,0))),((2,2),(1834,(0,0))),((3,-1),(2363,(0,1))),((3,3),(1849,(0,0))),((4,-1),(2374,(0,1))),((4,1),(1853,(0,0))),((4,2),(1854,(0,0))),((5,0),(1855,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_555_checked : successorFastRowCheck layer8 row7_555 row7_555choice = true := by decide
def row7_556 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)]
def row7_556choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1878,(1,0))),((0,0),(673,(0,0))),((0,2),(1375,(0,0))),((1,0),(1651,(0,0))),((1,2),(1732,(0,0))),((2,0),(1798,(0,0))),((2,2),(1835,(0,0))),((3,-1),(2364,(0,1))),((3,3),(1850,(0,0))),((4,0),(1853,(0,0))),((4,2),(1856,(0,0))),((5,1),(1857,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_556_checked : successorFastRowCheck layer8 row7_556 row7_556choice = true := by decide
def row7_557 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]
def row7_557choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1879,(1,0))),((0,0),(674,(0,0))),((0,2),(1376,(0,0))),((1,0),(1652,(0,0))),((1,2),(1733,(0,0))),((2,0),(1799,(0,0))),((2,2),(1836,(0,0))),((3,-1),(2365,(0,1))),((3,3),(1851,(0,0))),((4,0),(1854,(0,0))),((4,1),(1856,(0,0))),((4,3),(1858,(0,0))),((5,2),(1859,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_557_checked : successorFastRowCheck layer8 row7_557 row7_557choice = true := by decide
def row7_558 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)]
def row7_558choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1880,(1,0))),((0,0),(675,(0,0))),((0,2),(1377,(0,0))),((1,0),(1653,(0,0))),((1,2),(1734,(0,0))),((2,0),(1800,(0,0))),((2,2),(1837,(0,0))),((3,-1),(2369,(0,1))),((3,2),(1853,(0,0))),((4,-1),(2375,(0,1))),((4,2),(1860,(0,0))),((5,0),(1861,(0,0))),((5,1),(1862,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_558_checked : successorFastRowCheck layer8 row7_558 row7_558choice = true := by decide
def row7_559 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]
def row7_559choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1881,(1,0))),((0,0),(676,(0,0))),((0,2),(1378,(0,0))),((1,0),(1654,(0,0))),((1,2),(1735,(0,0))),((2,0),(1801,(0,0))),((2,2),(1838,(0,0))),((3,-1),(2370,(0,1))),((3,2),(1855,(0,0))),((4,-1),(2377,(0,1))),((4,1),(1861,(0,0))),((5,-1),(2378,(0,1))),((5,1),(1863,(0,0))),((6,0),(1864,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_559_checked : successorFastRowCheck layer8 row7_559 row7_559choice = true := by decide
def Closure7C069rows : List (List GridPoint) := [row7_552,row7_553,row7_554,row7_555,row7_556,row7_557,row7_558,row7_559]
theorem Closure7C069_closed : ∀ row ∈ Closure7C069rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C069rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_552choice,row7_552_checked⟩
  · subst row
    exact ⟨row7_553choice,row7_553_checked⟩
  · subst row
    exact ⟨row7_554choice,row7_554_checked⟩
  · subst row
    exact ⟨row7_555choice,row7_555_checked⟩
  · subst row
    exact ⟨row7_556choice,row7_556_checked⟩
  · subst row
    exact ⟨row7_557choice,row7_557_checked⟩
  · subst row
    exact ⟨row7_558choice,row7_558_checked⟩
  · subst row
    exact ⟨row7_559choice,row7_559_checked⟩
end Polyomino57
