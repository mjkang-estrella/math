import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_544 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)]
def row7_544choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1866,(1,0))),((0,0),(637,(0,0))),((0,2),(1363,(0,0))),((1,0),(1601,(0,0))),((1,2),(1719,(0,0))),((2,-1),(2324,(0,1))),((2,2),(1784,(0,0))),((3,0),(1798,(0,0))),((3,3),(1810,(0,0))),((4,0),(1813,(0,0))),((4,2),(1814,(0,0))),((5,1),(1815,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_544_checked : successorFastRowCheck layer8 row7_544 row7_544choice = true := by decide
def row7_545 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]
def row7_545choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1867,(1,0))),((0,0),(638,(0,0))),((0,2),(1364,(0,0))),((1,0),(1602,(0,0))),((1,2),(1720,(0,0))),((2,-1),(2325,(0,1))),((2,2),(1785,(0,0))),((3,0),(1799,(0,0))),((3,3),(1811,(0,0))),((4,1),(1814,(0,0))),((4,3),(1816,(0,0))),((5,2),(1817,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_545_checked : successorFastRowCheck layer8 row7_545 row7_545choice = true := by decide
def row7_546 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)]
def row7_546choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1868,(1,0))),((0,0),(639,(0,0))),((0,2),(1365,(0,0))),((1,0),(1603,(0,0))),((1,2),(1721,(0,0))),((2,-1),(2326,(0,1))),((2,2),(1786,(0,0))),((3,0),(1800,(0,0))),((3,2),(1813,(0,0))),((4,-1),(2353,(0,1))),((4,2),(1818,(0,0))),((5,0),(1819,(0,0))),((5,1),(1820,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_546_checked : successorFastRowCheck layer8 row7_546 row7_546choice = true := by decide
def row7_547 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)]
def row7_547choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1869,(1,0))),((0,0),(640,(0,0))),((0,2),(1366,(0,0))),((1,0),(1604,(0,0))),((1,2),(1722,(0,0))),((2,-1),(2327,(0,1))),((2,2),(1787,(0,0))),((3,0),(1802,(0,0))),((3,2),(1814,(0,0))),((4,0),(1818,(0,0))),((4,3),(1821,(0,0))),((5,1),(1822,(0,0))),((5,2),(1823,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_547_checked : successorFastRowCheck layer8 row7_547 row7_547choice = true := by decide
def row7_548 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]
def row7_548choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1870,(1,0))),((0,0),(641,(0,0))),((0,2),(1367,(0,0))),((1,0),(1605,(0,0))),((1,2),(1723,(0,0))),((2,-1),(2328,(0,1))),((2,2),(1788,(0,0))),((3,0),(1803,(0,0))),((3,2),(1815,(0,0))),((4,0),(1820,(0,0))),((4,2),(1822,(0,0))),((5,0),(1824,(0,0))),((5,2),(1825,(0,0))),((6,1),(1826,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_548_checked : successorFastRowCheck layer8 row7_548 row7_548choice = true := by decide
def row7_549 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)]
def row7_549choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1871,(1,0))),((0,0),(647,(0,0))),((0,2),(1368,(0,0))),((1,0),(1625,(0,0))),((1,2),(1725,(0,0))),((1,3),(1756,(0,0))),((2,0),(1764,(0,0))),((2,4),(1827,(0,0))),((3,-1),(2354,(0,1))),((3,2),(1828,(0,0))),((3,3),(1829,(0,0))),((4,0),(1830,(0,0))),((4,1),(1831,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_549_checked : successorFastRowCheck layer8 row7_549 row7_549choice = true := by decide
def row7_550 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)]
def row7_550choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1872,(1,0))),((0,0),(655,(0,0))),((0,2),(1369,(0,0))),((1,0),(1633,(0,0))),((1,2),(1726,(0,0))),((2,0),(1775,(0,0))),((2,3),(1828,(0,0))),((3,-1),(2355,(0,1))),((3,3),(1833,(0,0))),((4,0),(1834,(0,0))),((4,1),(1835,(0,0))),((4,2),(1836,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_550_checked : successorFastRowCheck layer8 row7_550 row7_550choice = true := by decide
def row7_551 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)]
def row7_551choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1873,(1,0))),((0,0),(656,(0,0))),((0,2),(1370,(0,0))),((1,0),(1634,(0,0))),((1,2),(1727,(0,0))),((2,0),(1776,(0,0))),((2,3),(1830,(0,0))),((3,-1),(2357,(0,1))),((3,2),(1834,(0,0))),((4,-1),(2359,(0,1))),((4,1),(1837,(0,0))),((5,0),(1838,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_551_checked : successorFastRowCheck layer8 row7_551 row7_551choice = true := by decide
def Closure7C068rows : List (List GridPoint) := [row7_544,row7_545,row7_546,row7_547,row7_548,row7_549,row7_550,row7_551]
theorem Closure7C068_closed : ∀ row ∈ Closure7C068rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C068rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_544choice,row7_544_checked⟩
  · subst row
    exact ⟨row7_545choice,row7_545_checked⟩
  · subst row
    exact ⟨row7_546choice,row7_546_checked⟩
  · subst row
    exact ⟨row7_547choice,row7_547_checked⟩
  · subst row
    exact ⟨row7_548choice,row7_548_checked⟩
  · subst row
    exact ⟨row7_549choice,row7_549_checked⟩
  · subst row
    exact ⟨row7_550choice,row7_550_checked⟩
  · subst row
    exact ⟨row7_551choice,row7_551_checked⟩
end Polyomino57
