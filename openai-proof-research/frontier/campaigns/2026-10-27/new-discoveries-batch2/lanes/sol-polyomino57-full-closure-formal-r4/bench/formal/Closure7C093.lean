import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_744 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]
def row7_744choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2629,(1,0))),((0,2),(2033,(0,0))),((0,4),(2435,(0,0))),((1,0),(2513,(0,0))),((1,1),(2545,(0,0))),((1,2),(2559,(0,0))),((1,4),(2586,(0,0))),((2,-1),(2706,(0,1))),((2,4),(2594,(0,0))),((3,0),(2598,(0,0))),((3,1),(2601,(0,0))),((3,2),(2603,(0,0))),((3,4),(2605,(0,0))),((4,3),(2606,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_744_checked : successorFastRowCheck layer8 row7_744 row7_744choice = true := by decide
def row7_745 : List GridPoint := [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)]
def row7_745choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2630,(1,0))),((0,2),(2034,(0,0))),((0,4),(2436,(0,0))),((1,1),(2546,(0,0))),((1,2),(2568,(0,0))),((1,4),(2587,(0,0))),((2,0),(2596,(0,0))),((2,4),(2610,(0,0))),((3,-1),(2708,(0,1))),((3,2),(2611,(0,0))),((3,3),(2612,(0,0))),((4,0),(2613,(0,0))),((4,1),(2614,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_745_checked : successorFastRowCheck layer8 row7_745 row7_745choice = true := by decide
def row7_746 : List GridPoint := [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)]
def row7_746choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2631,(1,0))),((0,2),(2035,(0,0))),((0,4),(2437,(0,0))),((1,2),(2573,(0,0))),((1,4),(2588,(0,0))),((2,0),(2608,(0,0))),((2,1),(2611,(0,0))),((2,4),(2617,(0,0))),((3,-1),(2709,(0,1))),((3,3),(2618,(0,0))),((4,0),(2619,(0,0))),((4,1),(2620,(0,0))),((4,2),(2621,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_746_checked : successorFastRowCheck layer8 row7_746 row7_746choice = true := by decide
def row7_747 : List GridPoint := [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)]
def row7_747choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2632,(1,0))),((0,2),(2036,(0,0))),((0,4),(2438,(0,0))),((1,2),(2580,(0,0))),((1,4),(2589,(0,0))),((2,0),(2609,(0,0))),((2,1),(2616,(0,0))),((2,2),(2618,(0,0))),((2,4),(2624,(0,0))),((3,-1),(2710,(0,1))),((3,4),(2625,(0,0))),((4,0),(2626,(0,0))),((4,1),(2627,(0,0))),((4,2),(2628,(0,0))),((4,3),(2629,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_747_checked : successorFastRowCheck layer8 row7_747 row7_747choice = true := by decide
def row7_748 : List GridPoint := [(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_748choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2700,(1,0))),((-1,5),(2722,(1,0))),((0,0),(785,(0,0))),((0,1),(1450,(0,0))),((0,2),(2037,(0,0))),((0,3),(2387,(0,0))),((0,6),(2633,(0,0))),((1,-1),(2711,(0,1))),((1,5),(2634,(0,0))),((2,0),(2635,(0,0))),((2,1),(2636,(0,0))),((2,2),(2637,(0,0))),((2,3),(2638,(0,0))),((2,4),(2639,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_748_checked : successorFastRowCheck layer8 row7_748 row7_748choice = true := by decide
def row7_749 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_749choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2701,(1,0))),((0,0),(786,(0,0))),((0,1),(1451,(0,0))),((0,2),(2038,(0,0))),((0,3),(2396,(0,0))),((0,5),(2634,(0,0))),((1,-1),(2712,(0,1))),((1,6),(2644,(0,0))),((2,0),(2645,(0,0))),((2,1),(2646,(0,0))),((2,2),(2647,(0,0))),((2,3),(2648,(0,0))),((2,4),(2649,(0,0))),((2,5),(2650,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_749_checked : successorFastRowCheck layer8 row7_749 row7_749choice = true := by decide
def row7_750 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def row7_750choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2702,(1,0))),((0,0),(787,(0,0))),((0,1),(1452,(0,0))),((0,2),(2039,(0,0))),((0,3),(2397,(0,0))),((0,5),(2635,(0,0))),((1,-1),(2714,(0,1))),((1,5),(2645,(0,0))),((2,-1),(2719,(0,1))),((2,1),(2651,(0,0))),((2,2),(2652,(0,0))),((2,3),(2653,(0,0))),((2,4),(2654,(0,0))),((3,0),(2655,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_750_checked : successorFastRowCheck layer8 row7_750 row7_750choice = true := by decide
def row7_751 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_751choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2703,(1,0))),((0,0),(788,(0,0))),((0,1),(1453,(0,0))),((0,2),(2040,(0,0))),((0,3),(2398,(0,0))),((0,5),(2636,(0,0))),((1,-1),(2715,(0,1))),((1,5),(2646,(0,0))),((2,0),(2651,(0,0))),((2,2),(2656,(0,0))),((2,3),(2657,(0,0))),((2,4),(2658,(0,0))),((3,1),(2659,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_751_checked : successorFastRowCheck layer8 row7_751 row7_751choice = true := by decide
def Closure7C093rows : List (List GridPoint) := [row7_744,row7_745,row7_746,row7_747,row7_748,row7_749,row7_750,row7_751]
theorem Closure7C093_closed : ∀ row ∈ Closure7C093rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C093rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_744choice,row7_744_checked⟩
  · subst row
    exact ⟨row7_745choice,row7_745_checked⟩
  · subst row
    exact ⟨row7_746choice,row7_746_checked⟩
  · subst row
    exact ⟨row7_747choice,row7_747_checked⟩
  · subst row
    exact ⟨row7_748choice,row7_748_checked⟩
  · subst row
    exact ⟨row7_749choice,row7_749_checked⟩
  · subst row
    exact ⟨row7_750choice,row7_750_checked⟩
  · subst row
    exact ⟨row7_751choice,row7_751_checked⟩
end Polyomino57
