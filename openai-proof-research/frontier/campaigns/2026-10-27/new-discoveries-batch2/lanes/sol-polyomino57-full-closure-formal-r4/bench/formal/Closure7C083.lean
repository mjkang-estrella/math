import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_664 : List GridPoint := [(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]
def row7_664choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2354,(1,0))),((0,1),(1386,(0,0))),((0,3),(1996,(0,0))),((0,4),(2045,(0,0))),((1,0),(2164,(0,0))),((1,1),(2183,(0,0))),((1,5),(2257,(0,0))),((2,-1),(2581,(0,1))),((2,3),(2258,(0,0))),((2,4),(2259,(0,0))),((3,0),(2260,(0,0))),((3,1),(2261,(0,0))),((3,2),(2262,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_664_checked : successorFastRowCheck layer8 row7_664 row7_664choice = true := by decide
def row7_665 : List GridPoint := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_665choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2355,(1,0))),((0,1),(1387,(0,0))),((0,3),(1997,(0,0))),((1,0),(2165,(0,0))),((1,1),(2189,(0,0))),((1,4),(2258,(0,0))),((2,-1),(2582,(0,1))),((2,4),(2265,(0,0))),((3,0),(2266,(0,0))),((3,1),(2267,(0,0))),((3,2),(2268,(0,0))),((3,3),(2269,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_665_checked : successorFastRowCheck layer8 row7_665 row7_665choice = true := by decide
def row7_666 : List GridPoint := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)]
def row7_666choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2356,(1,0))),((0,1),(1388,(0,0))),((0,3),(1998,(0,0))),((1,0),(2166,(0,0))),((1,1),(2190,(0,0))),((1,4),(2260,(0,0))),((2,-1),(2584,(0,1))),((2,3),(2266,(0,0))),((3,-1),(2587,(0,1))),((3,1),(2270,(0,0))),((3,2),(2271,(0,0))),((4,0),(2272,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_666_checked : successorFastRowCheck layer8 row7_666 row7_666choice = true := by decide
def row7_667 : List GridPoint := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)]
def row7_667choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2357,(1,0))),((0,1),(1389,(0,0))),((0,3),(1999,(0,0))),((1,0),(2167,(0,0))),((1,1),(2191,(0,0))),((1,4),(2261,(0,0))),((2,-1),(2585,(0,1))),((2,3),(2267,(0,0))),((3,0),(2270,(0,0))),((3,2),(2273,(0,0))),((4,1),(2274,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_667_checked : successorFastRowCheck layer8 row7_667 row7_667choice = true := by decide
def row7_668 : List GridPoint := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]
def row7_668choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2358,(1,0))),((0,1),(1390,(0,0))),((0,3),(2000,(0,0))),((1,0),(2168,(0,0))),((1,1),(2192,(0,0))),((1,4),(2262,(0,0))),((2,-1),(2586,(0,1))),((2,3),(2268,(0,0))),((3,0),(2271,(0,0))),((3,1),(2273,(0,0))),((3,3),(2275,(0,0))),((4,2),(2276,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_668_checked : successorFastRowCheck layer8 row7_668 row7_668choice = true := by decide
def row7_669 : List GridPoint := [(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)]
def row7_669choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2359,(1,0))),((0,1),(1391,(0,0))),((0,3),(2001,(0,0))),((1,1),(2201,(0,0))),((1,4),(2263,(0,0))),((2,0),(2270,(0,0))),((2,3),(2278,(0,0))),((3,-1),(2588,(0,1))),((3,2),(2279,(0,0))),((4,0),(2280,(0,0))),((4,1),(2281,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_669_checked : successorFastRowCheck layer8 row7_669 row7_669choice = true := by decide
def row7_670 : List GridPoint := [(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)]
def row7_670choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2360,(1,0))),((0,1),(1392,(0,0))),((0,3),(2002,(0,0))),((1,1),(2207,(0,0))),((1,4),(2264,(0,0))),((2,0),(2277,(0,0))),((2,1),(2279,(0,0))),((2,3),(2283,(0,0))),((3,-1),(2589,(0,1))),((3,3),(2284,(0,0))),((4,0),(2285,(0,0))),((4,1),(2286,(0,0))),((4,2),(2287,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_670_checked : successorFastRowCheck layer8 row7_670 row7_670choice = true := by decide
def row7_671 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)]
def row7_671choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2361,(1,0))),((0,1),(1393,(0,0))),((0,3),(2003,(0,0))),((1,0),(2169,(0,0))),((1,1),(2208,(0,0))),((1,3),(2265,(0,0))),((1,4),(2291,(0,0))),((2,-1),(2590,(0,1))),((2,5),(2292,(0,0))),((3,0),(2293,(0,0))),((3,1),(2294,(0,0))),((3,2),(2295,(0,0))),((3,3),(2296,(0,0))),((3,4),(2297,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_671_checked : successorFastRowCheck layer8 row7_671 row7_671choice = true := by decide
def Closure7C083rows : List (List GridPoint) := [row7_664,row7_665,row7_666,row7_667,row7_668,row7_669,row7_670,row7_671]
theorem Closure7C083_closed : ∀ row ∈ Closure7C083rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C083rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_664choice,row7_664_checked⟩
  · subst row
    exact ⟨row7_665choice,row7_665_checked⟩
  · subst row
    exact ⟨row7_666choice,row7_666_checked⟩
  · subst row
    exact ⟨row7_667choice,row7_667_checked⟩
  · subst row
    exact ⟨row7_668choice,row7_668_checked⟩
  · subst row
    exact ⟨row7_669choice,row7_669_checked⟩
  · subst row
    exact ⟨row7_670choice,row7_670_checked⟩
  · subst row
    exact ⟨row7_671choice,row7_671_checked⟩
end Polyomino57
