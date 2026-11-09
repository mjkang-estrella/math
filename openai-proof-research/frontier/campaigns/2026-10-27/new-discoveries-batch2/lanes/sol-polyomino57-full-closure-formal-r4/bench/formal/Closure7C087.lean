import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_696 : List GridPoint := [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)]
def row7_696choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2581,(1,0))),((-1,4),(2691,(1,0))),((-1,5),(2721,(1,0))),((0,0),(759,(0,0))),((0,1),(1418,(0,0))),((0,2),(1890,(0,0))),((0,6),(2386,(0,0))),((1,-1),(2633,(0,1))),((1,4),(2387,(0,0))),((1,5),(2388,(0,0))),((2,0),(2389,(0,0))),((2,1),(2390,(0,0))),((2,2),(2391,(0,0))),((2,3),(2392,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_696_checked : successorFastRowCheck layer8 row7_696 row7_696choice = true := by decide
def row7_697 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_697choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2582,(1,0))),((-1,4),(2692,(1,0))),((0,0),(760,(0,0))),((0,1),(1419,(0,0))),((0,2),(1898,(0,0))),((0,5),(2387,(0,0))),((1,-1),(2634,(0,1))),((1,5),(2396,(0,0))),((2,0),(2397,(0,0))),((2,1),(2398,(0,0))),((2,2),(2399,(0,0))),((2,3),(2400,(0,0))),((2,4),(2401,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_697_checked : successorFastRowCheck layer8 row7_697 row7_697choice = true := by decide
def row7_698 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row7_698choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2583,(1,0))),((-1,4),(2693,(1,0))),((0,0),(761,(0,0))),((0,1),(1420,(0,0))),((0,2),(1899,(0,0))),((0,5),(2389,(0,0))),((1,-1),(2636,(0,1))),((1,4),(2397,(0,0))),((2,-1),(2640,(0,1))),((2,1),(2402,(0,0))),((2,2),(2403,(0,0))),((2,3),(2404,(0,0))),((3,0),(2405,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_698_checked : successorFastRowCheck layer8 row7_698 row7_698choice = true := by decide
def row7_699 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row7_699choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2584,(1,0))),((-1,4),(2694,(1,0))),((0,0),(762,(0,0))),((0,1),(1421,(0,0))),((0,2),(1900,(0,0))),((0,5),(2390,(0,0))),((1,-1),(2637,(0,1))),((1,4),(2398,(0,0))),((2,0),(2402,(0,0))),((2,2),(2406,(0,0))),((2,3),(2407,(0,0))),((3,1),(2408,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_699_checked : successorFastRowCheck layer8 row7_699 row7_699choice = true := by decide
def row7_700 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row7_700choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2585,(1,0))),((-1,4),(2695,(1,0))),((0,0),(763,(0,0))),((0,1),(1422,(0,0))),((0,2),(1901,(0,0))),((0,5),(2391,(0,0))),((1,-1),(2638,(0,1))),((1,4),(2399,(0,0))),((2,0),(2403,(0,0))),((2,1),(2406,(0,0))),((2,3),(2409,(0,0))),((3,2),(2410,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_700_checked : successorFastRowCheck layer8 row7_700 row7_700choice = true := by decide
def row7_701 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_701choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2586,(1,0))),((-1,4),(2696,(1,0))),((0,0),(764,(0,0))),((0,1),(1423,(0,0))),((0,2),(1902,(0,0))),((0,5),(2392,(0,0))),((1,-1),(2639,(0,1))),((1,4),(2400,(0,0))),((2,0),(2404,(0,0))),((2,1),(2407,(0,0))),((2,2),(2409,(0,0))),((2,4),(2411,(0,0))),((3,3),(2412,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_701_checked : successorFastRowCheck layer8 row7_701 row7_701choice = true := by decide
def row7_702 : List GridPoint := [(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_702choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2587,(1,0))),((-1,4),(2697,(1,0))),((0,1),(1424,(0,0))),((0,2),(1916,(0,0))),((0,5),(2393,(0,0))),((1,0),(2402,(0,0))),((1,4),(2416,(0,0))),((2,-1),(2641,(0,1))),((2,2),(2417,(0,0))),((2,3),(2418,(0,0))),((3,0),(2419,(0,0))),((3,1),(2420,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_702_checked : successorFastRowCheck layer8 row7_702 row7_702choice = true := by decide
def row7_703 : List GridPoint := [(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_703choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2588,(1,0))),((-1,4),(2698,(1,0))),((0,2),(1922,(0,0))),((0,5),(2394,(0,0))),((1,0),(2414,(0,0))),((1,1),(2417,(0,0))),((1,4),(2423,(0,0))),((2,-1),(2642,(0,1))),((2,3),(2424,(0,0))),((3,0),(2425,(0,0))),((3,1),(2426,(0,0))),((3,2),(2427,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_703_checked : successorFastRowCheck layer8 row7_703 row7_703choice = true := by decide
def Closure7C087rows : List (List GridPoint) := [row7_696,row7_697,row7_698,row7_699,row7_700,row7_701,row7_702,row7_703]
theorem Closure7C087_closed : ∀ row ∈ Closure7C087rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C087rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_696choice,row7_696_checked⟩
  · subst row
    exact ⟨row7_697choice,row7_697_checked⟩
  · subst row
    exact ⟨row7_698choice,row7_698_checked⟩
  · subst row
    exact ⟨row7_699choice,row7_699_checked⟩
  · subst row
    exact ⟨row7_700choice,row7_700_checked⟩
  · subst row
    exact ⟨row7_701choice,row7_701_checked⟩
  · subst row
    exact ⟨row7_702choice,row7_702_checked⟩
  · subst row
    exact ⟨row7_703choice,row7_703_checked⟩
end Polyomino57
