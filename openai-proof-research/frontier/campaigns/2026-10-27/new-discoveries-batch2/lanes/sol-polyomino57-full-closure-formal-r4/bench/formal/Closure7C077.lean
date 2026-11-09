import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_616 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def row7_616choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2306,(1,0))),((0,0),(731,(0,0))),((0,1),(1264,(0,0))),((0,3),(1945,(0,0))),((1,-1),(2461,(0,1))),((1,4),(2065,(0,0))),((2,0),(2076,(0,0))),((2,1),(2084,(0,0))),((2,3),(2092,(0,0))),((3,1),(2094,(0,0))),((3,3),(2095,(0,0))),((4,2),(2096,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_616_checked : successorFastRowCheck layer8 row7_616 row7_616choice = true := by decide
def row7_617 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def row7_617choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2307,(1,0))),((0,0),(732,(0,0))),((0,1),(1265,(0,0))),((0,3),(1946,(0,0))),((1,-1),(2462,(0,1))),((1,4),(2066,(0,0))),((2,0),(2077,(0,0))),((2,1),(2085,(0,0))),((2,2),(2091,(0,0))),((2,5),(2097,(0,0))),((3,3),(2098,(0,0))),((3,4),(2099,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_617_checked : successorFastRowCheck layer8 row7_617 row7_617choice = true := by decide
def row7_618 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def row7_618choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2308,(1,0))),((0,0),(733,(0,0))),((0,1),(1266,(0,0))),((0,3),(1947,(0,0))),((1,-1),(2463,(0,1))),((1,4),(2067,(0,0))),((2,0),(2079,(0,0))),((2,1),(2087,(0,0))),((2,2),(2093,(0,0))),((2,4),(2098,(0,0))),((3,2),(2100,(0,0))),((3,4),(2101,(0,0))),((4,3),(2102,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_618_checked : successorFastRowCheck layer8 row7_618 row7_618choice = true := by decide
def row7_619 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_619choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2309,(1,0))),((0,0),(734,(0,0))),((0,1),(1267,(0,0))),((0,3),(1948,(0,0))),((1,-1),(2476,(0,1))),((1,3),(2070,(0,0))),((2,-1),(2521,(0,1))),((2,3),(2104,(0,0))),((3,0),(2105,(0,0))),((3,1),(2106,(0,0))),((3,2),(2107,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_619_checked : successorFastRowCheck layer8 row7_619 row7_619choice = true := by decide
def row7_620 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_620choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2310,(1,0))),((0,0),(735,(0,0))),((0,1),(1268,(0,0))),((0,3),(1949,(0,0))),((1,-1),(2477,(0,1))),((1,3),(2072,(0,0))),((2,-1),(2523,(0,1))),((2,2),(2105,(0,0))),((3,-1),(2533,(0,1))),((3,1),(2108,(0,0))),((4,0),(2109,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_620_checked : successorFastRowCheck layer8 row7_620 row7_620choice = true := by decide
def row7_621 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_621choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2311,(1,0))),((0,0),(736,(0,0))),((0,1),(1269,(0,0))),((0,3),(1950,(0,0))),((1,-1),(2478,(0,1))),((1,3),(2073,(0,0))),((2,-1),(2524,(0,1))),((2,2),(2106,(0,0))),((3,0),(2108,(0,0))),((3,2),(2110,(0,0))),((4,1),(2111,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_621_checked : successorFastRowCheck layer8 row7_621 row7_621choice = true := by decide
def row7_622 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def row7_622choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2312,(1,0))),((0,0),(737,(0,0))),((0,1),(1270,(0,0))),((0,3),(1951,(0,0))),((1,-1),(2479,(0,1))),((1,3),(2074,(0,0))),((2,-1),(2525,(0,1))),((2,1),(2104,(0,0))),((2,4),(2112,(0,0))),((3,0),(2113,(0,0))),((3,2),(2114,(0,0))),((3,3),(2115,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_622_checked : successorFastRowCheck layer8 row7_622 row7_622choice = true := by decide
def row7_623 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def row7_623choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2313,(1,0))),((0,0),(738,(0,0))),((0,1),(1271,(0,0))),((0,3),(1952,(0,0))),((1,-1),(2480,(0,1))),((1,3),(2075,(0,0))),((2,-1),(2527,(0,1))),((2,1),(2105,(0,0))),((2,3),(2113,(0,0))),((3,-1),(2534,(0,1))),((3,1),(2116,(0,0))),((3,2),(2117,(0,0))),((4,0),(2118,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_623_checked : successorFastRowCheck layer8 row7_623 row7_623choice = true := by decide
def Closure7C077rows : List (List GridPoint) := [row7_616,row7_617,row7_618,row7_619,row7_620,row7_621,row7_622,row7_623]
theorem Closure7C077_closed : ∀ row ∈ Closure7C077rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C077rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_616choice,row7_616_checked⟩
  · subst row
    exact ⟨row7_617choice,row7_617_checked⟩
  · subst row
    exact ⟨row7_618choice,row7_618_checked⟩
  · subst row
    exact ⟨row7_619choice,row7_619_checked⟩
  · subst row
    exact ⟨row7_620choice,row7_620_checked⟩
  · subst row
    exact ⟨row7_621choice,row7_621_checked⟩
  · subst row
    exact ⟨row7_622choice,row7_622_checked⟩
  · subst row
    exact ⟨row7_623choice,row7_623_checked⟩
end Polyomino57
