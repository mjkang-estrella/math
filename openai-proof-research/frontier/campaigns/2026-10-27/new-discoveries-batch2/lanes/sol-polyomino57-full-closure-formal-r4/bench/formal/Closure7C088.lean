import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_704 : List GridPoint := [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_704choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2589,(1,0))),((-1,4),(2699,(1,0))),((0,2),(1930,(0,0))),((0,5),(2395,(0,0))),((1,0),(2415,(0,0))),((1,1),(2422,(0,0))),((1,2),(2424,(0,0))),((1,4),(2430,(0,0))),((2,-1),(2643,(0,1))),((2,4),(2431,(0,0))),((3,0),(2432,(0,0))),((3,1),(2433,(0,0))),((3,2),(2434,(0,0))),((3,3),(2435,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_704_checked : successorFastRowCheck layer8 row7_704 row7_704choice = true := by decide
def row7_705 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_705choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2590,(1,0))),((0,0),(765,(0,0))),((0,1),(1425,(0,0))),((0,2),(1931,(0,0))),((0,4),(2396,(0,0))),((0,5),(2440,(0,0))),((1,-1),(2644,(0,1))),((1,6),(2441,(0,0))),((2,0),(2442,(0,0))),((2,1),(2443,(0,0))),((2,2),(2444,(0,0))),((2,3),(2445,(0,0))),((2,4),(2446,(0,0))),((2,5),(2447,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_705_checked : successorFastRowCheck layer8 row7_705 row7_705choice = true := by decide
def row7_706 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def row7_706choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2591,(1,0))),((0,0),(766,(0,0))),((0,1),(1426,(0,0))),((0,2),(1932,(0,0))),((0,4),(2397,(0,0))),((1,-1),(2646,(0,1))),((1,5),(2442,(0,0))),((2,-1),(2673,(0,1))),((2,1),(2448,(0,0))),((2,2),(2449,(0,0))),((2,3),(2450,(0,0))),((2,4),(2451,(0,0))),((3,0),(2452,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_706_checked : successorFastRowCheck layer8 row7_706 row7_706choice = true := by decide
def row7_707 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_707choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2592,(1,0))),((0,0),(767,(0,0))),((0,1),(1427,(0,0))),((0,2),(1933,(0,0))),((0,4),(2398,(0,0))),((1,-1),(2647,(0,1))),((1,5),(2443,(0,0))),((2,0),(2448,(0,0))),((2,2),(2453,(0,0))),((2,3),(2454,(0,0))),((2,4),(2455,(0,0))),((3,1),(2456,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_707_checked : successorFastRowCheck layer8 row7_707 row7_707choice = true := by decide
def row7_708 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_708choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2593,(1,0))),((0,0),(768,(0,0))),((0,1),(1428,(0,0))),((0,2),(1934,(0,0))),((0,4),(2399,(0,0))),((1,-1),(2648,(0,1))),((1,5),(2444,(0,0))),((2,0),(2449,(0,0))),((2,1),(2453,(0,0))),((2,3),(2457,(0,0))),((2,4),(2458,(0,0))),((3,2),(2459,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_708_checked : successorFastRowCheck layer8 row7_708 row7_708choice = true := by decide
def row7_709 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_709choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2594,(1,0))),((0,0),(769,(0,0))),((0,1),(1429,(0,0))),((0,2),(1935,(0,0))),((0,4),(2400,(0,0))),((1,-1),(2649,(0,1))),((1,5),(2445,(0,0))),((2,0),(2450,(0,0))),((2,1),(2454,(0,0))),((2,2),(2457,(0,0))),((2,4),(2460,(0,0))),((3,3),(2461,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_709_checked : successorFastRowCheck layer8 row7_709 row7_709choice = true := by decide
def row7_710 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_710choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2595,(1,0))),((0,0),(770,(0,0))),((0,1),(1430,(0,0))),((0,2),(1936,(0,0))),((0,4),(2401,(0,0))),((1,-1),(2650,(0,1))),((1,5),(2446,(0,0))),((2,0),(2451,(0,0))),((2,1),(2455,(0,0))),((2,2),(2458,(0,0))),((2,3),(2460,(0,0))),((2,5),(2462,(0,0))),((3,4),(2463,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_710_checked : successorFastRowCheck layer8 row7_710 row7_710choice = true := by decide
def row7_711 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_711choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2596,(1,0))),((0,0),(771,(0,0))),((0,1),(1431,(0,0))),((0,2),(1937,(0,0))),((0,4),(2402,(0,0))),((1,-1),(2656,(0,1))),((1,4),(2448,(0,0))),((2,-1),(2674,(0,1))),((2,2),(2464,(0,0))),((2,3),(2465,(0,0))),((3,0),(2466,(0,0))),((3,1),(2467,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_711_checked : successorFastRowCheck layer8 row7_711 row7_711choice = true := by decide
def Closure7C088rows : List (List GridPoint) := [row7_704,row7_705,row7_706,row7_707,row7_708,row7_709,row7_710,row7_711]
theorem Closure7C088_closed : ∀ row ∈ Closure7C088rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C088rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_704choice,row7_704_checked⟩
  · subst row
    exact ⟨row7_705choice,row7_705_checked⟩
  · subst row
    exact ⟨row7_706choice,row7_706_checked⟩
  · subst row
    exact ⟨row7_707choice,row7_707_checked⟩
  · subst row
    exact ⟨row7_708choice,row7_708_checked⟩
  · subst row
    exact ⟨row7_709choice,row7_709_checked⟩
  · subst row
    exact ⟨row7_710choice,row7_710_checked⟩
  · subst row
    exact ⟨row7_711choice,row7_711_checked⟩
end Polyomino57
