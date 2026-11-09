import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_512 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_512choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1834,(1,0))),((0,0),(568,(0,0))),((0,2),(1331,(0,0))),((1,0),(1517,(0,0))),((1,3),(1683,(0,0))),((2,-1),(2267,(0,1))),((2,3),(1702,(0,0))),((3,-1),(2278,(0,1))),((3,1),(1706,(0,0))),((3,2),(1707,(0,0))),((4,0),(1708,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_512_checked : successorFastRowCheck layer8 row7_512 row7_512choice = true := by decide
def row7_513 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_513choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1835,(1,0))),((0,0),(569,(0,0))),((0,2),(1332,(0,0))),((1,0),(1518,(0,0))),((1,3),(1684,(0,0))),((2,-1),(2268,(0,1))),((2,3),(1703,(0,0))),((3,0),(1706,(0,0))),((3,2),(1709,(0,0))),((4,1),(1710,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_513_checked : successorFastRowCheck layer8 row7_513 row7_513choice = true := by decide
def row7_514 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_514choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1836,(1,0))),((0,0),(570,(0,0))),((0,2),(1333,(0,0))),((1,0),(1519,(0,0))),((1,3),(1685,(0,0))),((2,-1),(2269,(0,1))),((2,3),(1704,(0,0))),((3,0),(1707,(0,0))),((3,1),(1709,(0,0))),((3,3),(1711,(0,0))),((4,2),(1712,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_514_checked : successorFastRowCheck layer8 row7_514 row7_514choice = true := by decide
def row7_515 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)]
def row7_515choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1837,(1,0))),((0,0),(571,(0,0))),((0,2),(1334,(0,0))),((1,0),(1520,(0,0))),((1,3),(1690,(0,0))),((2,-1),(2273,(0,1))),((2,2),(1706,(0,0))),((3,-1),(2279,(0,1))),((3,2),(1713,(0,0))),((4,0),(1714,(0,0))),((4,1),(1715,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_515_checked : successorFastRowCheck layer8 row7_515 row7_515choice = true := by decide
def row7_516 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]
def row7_516choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1838,(1,0))),((0,0),(572,(0,0))),((0,2),(1335,(0,0))),((1,0),(1521,(0,0))),((1,3),(1691,(0,0))),((2,-1),(2274,(0,1))),((2,2),(1708,(0,0))),((3,-1),(2281,(0,1))),((3,1),(1714,(0,0))),((4,-1),(2282,(0,1))),((4,1),(1716,(0,0))),((5,0),(1717,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_516_checked : successorFastRowCheck layer8 row7_516 row7_516choice = true := by decide
def row7_517 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)]
def row7_517choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1839,(1,0))),((0,0),(573,(0,0))),((0,2),(1336,(0,0))),((1,0),(1522,(0,0))),((1,3),(1692,(0,0))),((2,-1),(2275,(0,1))),((2,2),(1709,(0,0))),((3,0),(1713,(0,0))),((3,3),(1718,(0,0))),((4,1),(1719,(0,0))),((4,2),(1720,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_517_checked : successorFastRowCheck layer8 row7_517 row7_517choice = true := by decide
def row7_518 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]
def row7_518choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1840,(1,0))),((0,0),(574,(0,0))),((0,2),(1337,(0,0))),((1,0),(1523,(0,0))),((1,3),(1693,(0,0))),((2,-1),(2276,(0,1))),((2,2),(1710,(0,0))),((3,0),(1715,(0,0))),((3,2),(1719,(0,0))),((4,0),(1721,(0,0))),((4,2),(1722,(0,0))),((5,1),(1723,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_518_checked : successorFastRowCheck layer8 row7_518 row7_518choice = true := by decide
def row7_519 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)]
def row7_519choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1841,(1,0))),((0,0),(579,(0,0))),((0,2),(1338,(0,0))),((1,0),(1543,(0,0))),((1,3),(1694,(0,0))),((2,0),(1706,(0,0))),((2,3),(1725,(0,0))),((3,-1),(2283,(0,1))),((3,2),(1726,(0,0))),((4,0),(1727,(0,0))),((4,1),(1728,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_519_checked : successorFastRowCheck layer8 row7_519 row7_519choice = true := by decide
def Closure7C064rows : List (List GridPoint) := [row7_512,row7_513,row7_514,row7_515,row7_516,row7_517,row7_518,row7_519]
theorem Closure7C064_closed : ∀ row ∈ Closure7C064rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C064rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_512choice,row7_512_checked⟩
  · subst row
    exact ⟨row7_513choice,row7_513_checked⟩
  · subst row
    exact ⟨row7_514choice,row7_514_checked⟩
  · subst row
    exact ⟨row7_515choice,row7_515_checked⟩
  · subst row
    exact ⟨row7_516choice,row7_516_checked⟩
  · subst row
    exact ⟨row7_517choice,row7_517_checked⟩
  · subst row
    exact ⟨row7_518choice,row7_518_checked⟩
  · subst row
    exact ⟨row7_519choice,row7_519_checked⟩
end Polyomino57
