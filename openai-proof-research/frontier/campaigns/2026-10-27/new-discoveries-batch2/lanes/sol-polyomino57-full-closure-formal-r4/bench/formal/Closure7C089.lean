import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_712 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def row7_712choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2597,(1,0))),((0,0),(772,(0,0))),((0,1),(1432,(0,0))),((0,2),(1938,(0,0))),((0,4),(2403,(0,0))),((1,-1),(2657,(0,1))),((1,4),(2449,(0,0))),((2,-1),(2675,(0,1))),((2,1),(2464,(0,0))),((2,3),(2468,(0,0))),((3,0),(2469,(0,0))),((3,2),(2470,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_712_checked : successorFastRowCheck layer8 row7_712 row7_712choice = true := by decide
def row7_713 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def row7_713choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2598,(1,0))),((0,0),(773,(0,0))),((0,1),(1433,(0,0))),((0,2),(1939,(0,0))),((0,4),(2404,(0,0))),((1,-1),(2658,(0,1))),((1,4),(2450,(0,0))),((2,-1),(2676,(0,1))),((2,1),(2465,(0,0))),((2,2),(2468,(0,0))),((2,4),(2471,(0,0))),((3,0),(2472,(0,0))),((3,3),(2473,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_713_checked : successorFastRowCheck layer8 row7_713 row7_713choice = true := by decide
def row7_714 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def row7_714choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2599,(1,0))),((0,0),(774,(0,0))),((0,1),(1434,(0,0))),((0,2),(1940,(0,0))),((0,4),(2405,(0,0))),((1,-1),(2659,(0,1))),((1,4),(2452,(0,0))),((2,-1),(2678,(0,1))),((2,1),(2466,(0,0))),((2,2),(2469,(0,0))),((2,3),(2472,(0,0))),((3,-1),(2679,(0,1))),((3,1),(2474,(0,0))),((4,0),(2475,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_714_checked : successorFastRowCheck layer8 row7_714 row7_714choice = true := by decide
def row7_715 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def row7_715choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2600,(1,0))),((0,0),(775,(0,0))),((0,1),(1435,(0,0))),((0,2),(1941,(0,0))),((0,4),(2406,(0,0))),((1,-1),(2660,(0,1))),((1,4),(2453,(0,0))),((2,0),(2464,(0,0))),((2,3),(2476,(0,0))),((3,1),(2477,(0,0))),((3,2),(2478,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_715_checked : successorFastRowCheck layer8 row7_715 row7_715choice = true := by decide
def row7_716 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def row7_716choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2601,(1,0))),((0,0),(776,(0,0))),((0,1),(1436,(0,0))),((0,2),(1942,(0,0))),((0,4),(2407,(0,0))),((1,-1),(2661,(0,1))),((1,4),(2454,(0,0))),((2,0),(2465,(0,0))),((2,2),(2476,(0,0))),((2,4),(2479,(0,0))),((3,1),(2480,(0,0))),((3,3),(2481,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_716_checked : successorFastRowCheck layer8 row7_716 row7_716choice = true := by decide
def row7_717 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def row7_717choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2602,(1,0))),((0,0),(777,(0,0))),((0,1),(1437,(0,0))),((0,2),(1943,(0,0))),((0,4),(2408,(0,0))),((1,-1),(2662,(0,1))),((1,4),(2456,(0,0))),((2,0),(2467,(0,0))),((2,2),(2477,(0,0))),((2,3),(2480,(0,0))),((3,0),(2482,(0,0))),((3,2),(2483,(0,0))),((4,1),(2484,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_717_checked : successorFastRowCheck layer8 row7_717 row7_717choice = true := by decide
def row7_718 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def row7_718choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2603,(1,0))),((0,0),(778,(0,0))),((0,1),(1438,(0,0))),((0,2),(1944,(0,0))),((0,4),(2409,(0,0))),((1,-1),(2663,(0,1))),((1,4),(2457,(0,0))),((2,0),(2468,(0,0))),((2,1),(2476,(0,0))),((2,4),(2485,(0,0))),((3,2),(2486,(0,0))),((3,3),(2487,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_718_checked : successorFastRowCheck layer8 row7_718 row7_718choice = true := by decide
def row7_719 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def row7_719choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2604,(1,0))),((0,0),(779,(0,0))),((0,1),(1439,(0,0))),((0,2),(1945,(0,0))),((0,4),(2410,(0,0))),((1,-1),(2664,(0,1))),((1,4),(2459,(0,0))),((2,0),(2470,(0,0))),((2,1),(2478,(0,0))),((2,3),(2486,(0,0))),((3,1),(2488,(0,0))),((3,3),(2489,(0,0))),((4,2),(2490,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_719_checked : successorFastRowCheck layer8 row7_719 row7_719choice = true := by decide
def Closure7C089rows : List (List GridPoint) := [row7_712,row7_713,row7_714,row7_715,row7_716,row7_717,row7_718,row7_719]
theorem Closure7C089_closed : ∀ row ∈ Closure7C089rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C089rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_712choice,row7_712_checked⟩
  · subst row
    exact ⟨row7_713choice,row7_713_checked⟩
  · subst row
    exact ⟨row7_714choice,row7_714_checked⟩
  · subst row
    exact ⟨row7_715choice,row7_715_checked⟩
  · subst row
    exact ⟨row7_716choice,row7_716_checked⟩
  · subst row
    exact ⟨row7_717choice,row7_717_checked⟩
  · subst row
    exact ⟨row7_718choice,row7_718_checked⟩
  · subst row
    exact ⟨row7_719choice,row7_719_checked⟩
end Polyomino57
