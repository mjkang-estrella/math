import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_736 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]
def row7_736choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2621,(1,0))),((0,2),(2000,(0,0))),((0,4),(2427,(0,0))),((1,0),(2507,(0,0))),((1,1),(2524,(0,0))),((1,4),(2552,(0,0))),((2,-1),(2696,(0,1))),((2,3),(2558,(0,0))),((3,0),(2561,(0,0))),((3,1),(2563,(0,0))),((3,3),(2565,(0,0))),((4,2),(2566,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_736_checked : successorFastRowCheck layer8 row7_736 row7_736choice = true := by decide
def row7_737 : List GridPoint := [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)]
def row7_737choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2622,(1,0))),((0,2),(2001,(0,0))),((0,4),(2428,(0,0))),((1,1),(2533,(0,0))),((1,4),(2553,(0,0))),((2,0),(2560,(0,0))),((2,3),(2568,(0,0))),((3,-1),(2698,(0,1))),((3,2),(2569,(0,0))),((4,0),(2570,(0,0))),((4,1),(2571,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_737_checked : successorFastRowCheck layer8 row7_737 row7_737choice = true := by decide
def row7_738 : List GridPoint := [(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)]
def row7_738choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2623,(1,0))),((0,2),(2002,(0,0))),((0,4),(2429,(0,0))),((1,1),(2539,(0,0))),((1,4),(2554,(0,0))),((2,0),(2567,(0,0))),((2,1),(2569,(0,0))),((2,3),(2573,(0,0))),((3,-1),(2699,(0,1))),((3,3),(2574,(0,0))),((4,0),(2575,(0,0))),((4,1),(2576,(0,0))),((4,2),(2577,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_738_checked : successorFastRowCheck layer8 row7_738 row7_738choice = true := by decide
def row7_739 : List GridPoint := [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)]
def row7_739choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2624,(1,0))),((0,2),(2028,(0,0))),((0,4),(2430,(0,0))),((1,0),(2508,(0,0))),((1,1),(2540,(0,0))),((1,2),(2548,(0,0))),((1,5),(2581,(0,0))),((2,-1),(2700,(0,1))),((2,4),(2582,(0,0))),((3,0),(2583,(0,0))),((3,1),(2584,(0,0))),((3,2),(2585,(0,0))),((3,3),(2586,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_739_checked : successorFastRowCheck layer8 row7_739 row7_739choice = true := by decide
def row7_740 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)]
def row7_740choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2625,(1,0))),((0,2),(2029,(0,0))),((0,4),(2431,(0,0))),((1,0),(2509,(0,0))),((1,1),(2541,(0,0))),((1,2),(2555,(0,0))),((1,4),(2582,(0,0))),((2,-1),(2701,(0,1))),((2,5),(2590,(0,0))),((3,0),(2591,(0,0))),((3,1),(2592,(0,0))),((3,2),(2593,(0,0))),((3,3),(2594,(0,0))),((3,4),(2595,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_740_checked : successorFastRowCheck layer8 row7_740 row7_740choice = true := by decide
def row7_741 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)]
def row7_741choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2626,(1,0))),((0,2),(2030,(0,0))),((0,4),(2432,(0,0))),((1,0),(2510,(0,0))),((1,1),(2542,(0,0))),((1,2),(2556,(0,0))),((1,4),(2583,(0,0))),((2,-1),(2703,(0,1))),((2,4),(2591,(0,0))),((3,-1),(2707,(0,1))),((3,1),(2596,(0,0))),((3,2),(2597,(0,0))),((3,3),(2598,(0,0))),((4,0),(2599,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_741_checked : successorFastRowCheck layer8 row7_741 row7_741choice = true := by decide
def row7_742 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)]
def row7_742choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2627,(1,0))),((0,2),(2031,(0,0))),((0,4),(2433,(0,0))),((1,0),(2511,(0,0))),((1,1),(2543,(0,0))),((1,2),(2557,(0,0))),((1,4),(2584,(0,0))),((2,-1),(2704,(0,1))),((2,4),(2592,(0,0))),((3,0),(2596,(0,0))),((3,2),(2600,(0,0))),((3,3),(2601,(0,0))),((4,1),(2602,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_742_checked : successorFastRowCheck layer8 row7_742 row7_742choice = true := by decide
def row7_743 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)]
def row7_743choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2628,(1,0))),((0,2),(2032,(0,0))),((0,4),(2434,(0,0))),((1,0),(2512,(0,0))),((1,1),(2544,(0,0))),((1,2),(2558,(0,0))),((1,4),(2585,(0,0))),((2,-1),(2705,(0,1))),((2,4),(2593,(0,0))),((3,0),(2597,(0,0))),((3,1),(2600,(0,0))),((3,3),(2603,(0,0))),((4,2),(2604,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_743_checked : successorFastRowCheck layer8 row7_743 row7_743choice = true := by decide
def Closure7C092rows : List (List GridPoint) := [row7_736,row7_737,row7_738,row7_739,row7_740,row7_741,row7_742,row7_743]
theorem Closure7C092_closed : ∀ row ∈ Closure7C092rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C092rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_736choice,row7_736_checked⟩
  · subst row
    exact ⟨row7_737choice,row7_737_checked⟩
  · subst row
    exact ⟨row7_738choice,row7_738_checked⟩
  · subst row
    exact ⟨row7_739choice,row7_739_checked⟩
  · subst row
    exact ⟨row7_740choice,row7_740_checked⟩
  · subst row
    exact ⟨row7_741choice,row7_741_checked⟩
  · subst row
    exact ⟨row7_742choice,row7_742_checked⟩
  · subst row
    exact ⟨row7_743choice,row7_743_checked⟩
end Polyomino57
