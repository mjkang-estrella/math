import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_536 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)]
def row7_536choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1858,(1,0))),((0,0),(629,(0,0))),((0,2),(1355,(0,0))),((1,0),(1593,(0,0))),((1,2),(1711,(0,0))),((2,-1),(2307,(0,1))),((2,3),(1771,(0,0))),((3,0),(1778,(0,0))),((3,1),(1783,(0,0))),((3,4),(1789,(0,0))),((4,2),(1790,(0,0))),((4,3),(1791,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_536_checked : successorFastRowCheck layer8 row7_536 row7_536choice = true := by decide
def row7_537 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]
def row7_537choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1859,(1,0))),((0,0),(630,(0,0))),((0,2),(1356,(0,0))),((1,0),(1594,(0,0))),((1,2),(1712,(0,0))),((2,-1),(2308,(0,1))),((2,3),(1772,(0,0))),((3,0),(1780,(0,0))),((3,1),(1785,(0,0))),((3,3),(1790,(0,0))),((4,1),(1792,(0,0))),((4,3),(1793,(0,0))),((5,2),(1794,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_537_checked : successorFastRowCheck layer8 row7_537 row7_537choice = true := by decide
def row7_538 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)]
def row7_538choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1860,(1,0))),((0,0),(631,(0,0))),((0,2),(1357,(0,0))),((1,0),(1595,(0,0))),((1,2),(1713,(0,0))),((2,-1),(2317,(0,1))),((2,2),(1775,(0,0))),((3,-1),(2340,(0,1))),((3,3),(1796,(0,0))),((4,0),(1797,(0,0))),((4,1),(1798,(0,0))),((4,2),(1799,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_538_checked : successorFastRowCheck layer8 row7_538 row7_538choice = true := by decide
def row7_539 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)]
def row7_539choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1861,(1,0))),((0,0),(632,(0,0))),((0,2),(1358,(0,0))),((1,0),(1596,(0,0))),((1,2),(1714,(0,0))),((2,-1),(2318,(0,1))),((2,2),(1776,(0,0))),((3,-1),(2342,(0,1))),((3,2),(1797,(0,0))),((4,-1),(2348,(0,1))),((4,1),(1800,(0,0))),((5,0),(1801,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_539_checked : successorFastRowCheck layer8 row7_539 row7_539choice = true := by decide
def row7_540 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]
def row7_540choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1862,(1,0))),((0,0),(633,(0,0))),((0,2),(1359,(0,0))),((1,0),(1597,(0,0))),((1,2),(1715,(0,0))),((2,-1),(2319,(0,1))),((2,2),(1777,(0,0))),((3,-1),(2343,(0,1))),((3,2),(1798,(0,0))),((4,0),(1800,(0,0))),((4,2),(1802,(0,0))),((5,1),(1803,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_540_checked : successorFastRowCheck layer8 row7_540 row7_540choice = true := by decide
def row7_541 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)]
def row7_541choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1863,(1,0))),((0,0),(634,(0,0))),((0,2),(1360,(0,0))),((1,0),(1598,(0,0))),((1,2),(1716,(0,0))),((2,-1),(2321,(0,1))),((2,2),(1781,(0,0))),((3,-1),(2346,(0,1))),((3,1),(1800,(0,0))),((4,-1),(2349,(0,1))),((4,2),(1804,(0,0))),((5,0),(1805,(0,0))),((5,1),(1806,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_541_checked : successorFastRowCheck layer8 row7_541 row7_541choice = true := by decide
def row7_542 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]
def row7_542choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1864,(1,0))),((0,0),(635,(0,0))),((0,2),(1361,(0,0))),((1,0),(1599,(0,0))),((1,2),(1717,(0,0))),((2,-1),(2322,(0,1))),((2,2),(1782,(0,0))),((3,-1),(2347,(0,1))),((3,1),(1801,(0,0))),((4,-1),(2351,(0,1))),((4,1),(1805,(0,0))),((5,-1),(2352,(0,1))),((5,1),(1807,(0,0))),((6,0),(1808,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_542_checked : successorFastRowCheck layer8 row7_542 row7_542choice = true := by decide
def row7_543 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)]
def row7_543choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(1865,(1,0))),((0,0),(636,(0,0))),((0,2),(1362,(0,0))),((1,0),(1600,(0,0))),((1,2),(1718,(0,0))),((2,-1),(2323,(0,1))),((2,2),(1783,(0,0))),((2,3),(1795,(0,0))),((3,0),(1796,(0,0))),((3,4),(1809,(0,0))),((4,1),(1810,(0,0))),((4,2),(1811,(0,0))),((4,3),(1812,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_543_checked : successorFastRowCheck layer8 row7_543 row7_543choice = true := by decide
def Closure7C067rows : List (List GridPoint) := [row7_536,row7_537,row7_538,row7_539,row7_540,row7_541,row7_542,row7_543]
theorem Closure7C067_closed : ∀ row ∈ Closure7C067rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C067rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_536choice,row7_536_checked⟩
  · subst row
    exact ⟨row7_537choice,row7_537_checked⟩
  · subst row
    exact ⟨row7_538choice,row7_538_checked⟩
  · subst row
    exact ⟨row7_539choice,row7_539_checked⟩
  · subst row
    exact ⟨row7_540choice,row7_540_checked⟩
  · subst row
    exact ⟨row7_541choice,row7_541_checked⟩
  · subst row
    exact ⟨row7_542choice,row7_542_checked⟩
  · subst row
    exact ⟨row7_543choice,row7_543_checked⟩
end Polyomino57
