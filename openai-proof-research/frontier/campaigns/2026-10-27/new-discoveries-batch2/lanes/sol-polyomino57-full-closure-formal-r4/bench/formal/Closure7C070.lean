import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_560 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)]
def row7_560choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1882,(1,0))),((0,0),(677,(0,0))),((0,2),(1379,(0,0))),((1,0),(1655,(0,0))),((1,2),(1736,(0,0))),((2,0),(1802,(0,0))),((2,2),(1839,(0,0))),((3,-1),(2371,(0,1))),((3,2),(1856,(0,0))),((4,0),(1860,(0,0))),((4,3),(1865,(0,0))),((5,1),(1866,(0,0))),((5,2),(1867,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_560_checked : successorFastRowCheck layer8 row7_560 row7_560choice = true := by decide
def row7_561 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]
def row7_561choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1883,(1,0))),((0,0),(678,(0,0))),((0,2),(1380,(0,0))),((1,0),(1656,(0,0))),((1,2),(1737,(0,0))),((2,0),(1803,(0,0))),((2,2),(1840,(0,0))),((3,-1),(2372,(0,1))),((3,2),(1857,(0,0))),((4,0),(1862,(0,0))),((4,2),(1866,(0,0))),((5,0),(1868,(0,0))),((5,2),(1869,(0,0))),((6,1),(1870,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_561_checked : successorFastRowCheck layer8 row7_561 row7_561choice = true := by decide
def row7_562 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)]
def row7_562choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1884,(1,0))),((0,0),(683,(0,0))),((0,2),(1381,(0,0))),((1,0),(1661,(0,0))),((1,2),(1738,(0,0))),((2,0),(1813,(0,0))),((2,2),(1841,(0,0))),((3,0),(1853,(0,0))),((3,3),(1871,(0,0))),((4,-1),(2379,(0,1))),((4,2),(1872,(0,0))),((5,0),(1873,(0,0))),((5,1),(1874,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_562_checked : successorFastRowCheck layer8 row7_562 row7_562choice = true := by decide
def row7_563 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)]
def row7_563choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1885,(1,0))),((0,0),(688,(0,0))),((0,2),(1382,(0,0))),((1,0),(1666,(0,0))),((1,2),(1739,(0,0))),((2,0),(1818,(0,0))),((2,2),(1842,(0,0))),((3,0),(1860,(0,0))),((3,2),(1872,(0,0))),((4,-1),(2380,(0,1))),((4,3),(1876,(0,0))),((5,0),(1877,(0,0))),((5,1),(1878,(0,0))),((5,2),(1879,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_563_checked : successorFastRowCheck layer8 row7_563 row7_563choice = true := by decide
def row7_564 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)]
def row7_564choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1886,(1,0))),((0,0),(689,(0,0))),((0,2),(1383,(0,0))),((1,0),(1667,(0,0))),((1,2),(1740,(0,0))),((2,0),(1819,(0,0))),((2,2),(1843,(0,0))),((3,0),(1861,(0,0))),((3,2),(1873,(0,0))),((4,-1),(2382,(0,1))),((4,2),(1877,(0,0))),((5,-1),(2384,(0,1))),((5,1),(1880,(0,0))),((6,0),(1881,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_564_checked : successorFastRowCheck layer8 row7_564 row7_564choice = true := by decide
def row7_565 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]
def row7_565choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1887,(1,0))),((0,0),(690,(0,0))),((0,2),(1384,(0,0))),((1,0),(1668,(0,0))),((1,2),(1741,(0,0))),((2,0),(1820,(0,0))),((2,2),(1844,(0,0))),((3,0),(1862,(0,0))),((3,2),(1874,(0,0))),((4,-1),(2383,(0,1))),((4,2),(1878,(0,0))),((5,0),(1880,(0,0))),((5,2),(1882,(0,0))),((6,1),(1883,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_565_checked : successorFastRowCheck layer8 row7_565 row7_565choice = true := by decide
def row7_566 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)]
def row7_566choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1888,(1,0))),((0,0),(694,(0,0))),((0,2),(1385,(0,0))),((1,0),(1672,(0,0))),((1,2),(1742,(0,0))),((2,0),(1824,(0,0))),((2,2),(1845,(0,0))),((3,0),(1868,(0,0))),((3,2),(1875,(0,0))),((4,0),(1880,(0,0))),((4,2),(1884,(0,0))),((5,-1),(2385,(0,1))),((5,2),(1885,(0,0))),((6,0),(1886,(0,0))),((6,1),(1887,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_566_checked : successorFastRowCheck layer8 row7_566 row7_566choice = true := by decide
def row7_567 : List GridPoint := [(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)]
def row7_567choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2257,(1,0))),((-1,3),(2547,(1,0))),((-1,4),(2682,(1,0))),((-1,5),(2720,(1,0))),((0,0),(697,(0,0))),((0,1),(1147,(0,0))),((0,6),(1889,(0,0))),((1,-1),(2386,(0,1))),((1,3),(1890,(0,0))),((1,4),(1891,(0,0))),((1,5),(1892,(0,0))),((2,0),(1893,(0,0))),((2,1),(1894,(0,0))),((2,2),(1895,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_567_checked : successorFastRowCheck layer8 row7_567 row7_567choice = true := by decide
def Closure7C070rows : List (List GridPoint) := [row7_560,row7_561,row7_562,row7_563,row7_564,row7_565,row7_566,row7_567]
theorem Closure7C070_closed : ∀ row ∈ Closure7C070rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C070rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_560choice,row7_560_checked⟩
  · subst row
    exact ⟨row7_561choice,row7_561_checked⟩
  · subst row
    exact ⟨row7_562choice,row7_562_checked⟩
  · subst row
    exact ⟨row7_563choice,row7_563_checked⟩
  · subst row
    exact ⟨row7_564choice,row7_564_checked⟩
  · subst row
    exact ⟨row7_565choice,row7_565_checked⟩
  · subst row
    exact ⟨row7_566choice,row7_566_checked⟩
  · subst row
    exact ⟨row7_567choice,row7_567_checked⟩
end Polyomino57
