import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_488 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)]
def row7_488choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1810,(1,0))),((0,0),(463,(0,0))),((0,2),(1302,(0,0))),((1,-1),(2146,(0,1))),((1,2),(1540,(0,0))),((1,3),(1579,(0,0))),((2,0),(1585,(0,0))),((2,4),(1621,(0,0))),((3,0),(1625,(0,0))),((3,2),(1626,(0,0))),((3,3),(1627,(0,0))),((4,1),(1628,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_488_checked : successorFastRowCheck layer8 row7_488 row7_488choice = true := by decide
def row7_489 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)]
def row7_489choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1811,(1,0))),((0,0),(464,(0,0))),((0,2),(1303,(0,0))),((1,-1),(2147,(0,1))),((1,2),(1541,(0,0))),((1,3),(1580,(0,0))),((2,0),(1586,(0,0))),((2,4),(1622,(0,0))),((3,1),(1626,(0,0))),((3,3),(1629,(0,0))),((4,2),(1630,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_489_checked : successorFastRowCheck layer8 row7_489 row7_489choice = true := by decide
def row7_490 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]
def row7_490choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1812,(1,0))),((0,0),(465,(0,0))),((0,2),(1304,(0,0))),((1,-1),(2148,(0,1))),((1,2),(1542,(0,0))),((1,3),(1581,(0,0))),((2,0),(1587,(0,0))),((2,4),(1623,(0,0))),((3,1),(1627,(0,0))),((3,2),(1629,(0,0))),((3,4),(1631,(0,0))),((4,3),(1632,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_490_checked : successorFastRowCheck layer8 row7_490 row7_490choice = true := by decide
def row7_491 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)]
def row7_491choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1813,(1,0))),((0,0),(466,(0,0))),((0,2),(1305,(0,0))),((1,-1),(2149,(0,1))),((1,2),(1543,(0,0))),((2,0),(1588,(0,0))),((2,3),(1625,(0,0))),((3,-1),(2250,(0,1))),((3,2),(1633,(0,0))),((4,0),(1634,(0,0))),((4,1),(1635,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_491_checked : successorFastRowCheck layer8 row7_491 row7_491choice = true := by decide
def row7_492 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)]
def row7_492choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1814,(1,0))),((0,0),(467,(0,0))),((0,2),(1306,(0,0))),((1,-1),(2150,(0,1))),((1,2),(1544,(0,0))),((2,0),(1591,(0,0))),((2,3),(1626,(0,0))),((3,0),(1633,(0,0))),((3,3),(1636,(0,0))),((4,1),(1637,(0,0))),((4,2),(1638,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_492_checked : successorFastRowCheck layer8 row7_492 row7_492choice = true := by decide
def row7_493 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]
def row7_493choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1815,(1,0))),((0,0),(468,(0,0))),((0,2),(1307,(0,0))),((1,-1),(2151,(0,1))),((1,2),(1545,(0,0))),((2,0),(1592,(0,0))),((2,3),(1628,(0,0))),((3,0),(1635,(0,0))),((3,2),(1637,(0,0))),((4,0),(1639,(0,0))),((4,2),(1640,(0,0))),((5,1),(1641,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_493_checked : successorFastRowCheck layer8 row7_493 row7_493choice = true := by decide
def row7_494 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)]
def row7_494choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1816,(1,0))),((0,0),(469,(0,0))),((0,2),(1308,(0,0))),((1,-1),(2152,(0,1))),((1,2),(1546,(0,0))),((2,0),(1593,(0,0))),((2,3),(1629,(0,0))),((3,1),(1636,(0,0))),((3,4),(1642,(0,0))),((4,2),(1643,(0,0))),((4,3),(1644,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_494_checked : successorFastRowCheck layer8 row7_494 row7_494choice = true := by decide
def row7_495 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]
def row7_495choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1817,(1,0))),((0,0),(470,(0,0))),((0,2),(1309,(0,0))),((1,-1),(2153,(0,1))),((1,2),(1547,(0,0))),((2,0),(1594,(0,0))),((2,3),(1630,(0,0))),((3,1),(1638,(0,0))),((3,3),(1643,(0,0))),((4,1),(1645,(0,0))),((4,3),(1646,(0,0))),((5,2),(1647,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_495_checked : successorFastRowCheck layer8 row7_495 row7_495choice = true := by decide
def Closure7C061rows : List (List GridPoint) := [row7_488,row7_489,row7_490,row7_491,row7_492,row7_493,row7_494,row7_495]
theorem Closure7C061_closed : ∀ row ∈ Closure7C061rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C061rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_488choice,row7_488_checked⟩
  · subst row
    exact ⟨row7_489choice,row7_489_checked⟩
  · subst row
    exact ⟨row7_490choice,row7_490_checked⟩
  · subst row
    exact ⟨row7_491choice,row7_491_checked⟩
  · subst row
    exact ⟨row7_492choice,row7_492_checked⟩
  · subst row
    exact ⟨row7_493choice,row7_493_checked⟩
  · subst row
    exact ⟨row7_494choice,row7_494_checked⟩
  · subst row
    exact ⟨row7_495choice,row7_495_checked⟩
end Polyomino57
