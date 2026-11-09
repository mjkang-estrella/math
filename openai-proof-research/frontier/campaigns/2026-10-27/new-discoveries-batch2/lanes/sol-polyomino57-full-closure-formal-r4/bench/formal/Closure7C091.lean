import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_728 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]
def row7_728choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2613,(1,0))),((0,1),(1446,(0,0))),((0,2),(1978,(0,0))),((0,4),(2419,(0,0))),((1,0),(2466,(0,0))),((1,4),(2518,(0,0))),((2,-1),(2686,(0,1))),((2,2),(2522,(0,0))),((2,3),(2526,(0,0))),((3,-1),(2688,(0,1))),((3,1),(2529,(0,0))),((4,0),(2530,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_728_checked : successorFastRowCheck layer8 row7_728 row7_728choice = true := by decide
def row7_729 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]
def row7_729choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2614,(1,0))),((0,1),(1447,(0,0))),((0,2),(1979,(0,0))),((0,4),(2420,(0,0))),((1,0),(2467,(0,0))),((1,4),(2519,(0,0))),((2,-1),(2687,(0,1))),((2,2),(2523,(0,0))),((2,3),(2527,(0,0))),((3,0),(2529,(0,0))),((3,2),(2531,(0,0))),((4,1),(2532,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_729_checked : successorFastRowCheck layer8 row7_729 row7_729choice = true := by decide
def row7_730 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]
def row7_730choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2615,(1,0))),((0,1),(1448,(0,0))),((0,2),(1980,(0,0))),((0,4),(2421,(0,0))),((1,0),(2482,(0,0))),((1,4),(2520,(0,0))),((2,0),(2529,(0,0))),((2,2),(2533,(0,0))),((2,3),(2534,(0,0))),((3,-1),(2689,(0,1))),((3,2),(2535,(0,0))),((4,0),(2536,(0,0))),((4,1),(2537,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_730_checked : successorFastRowCheck layer8 row7_730 row7_730choice = true := by decide
def row7_731 : List GridPoint := [(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_731choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2616,(1,0))),((0,1),(1449,(0,0))),((0,2),(1995,(0,0))),((0,4),(2422,(0,0))),((1,0),(2498,(0,0))),((1,2),(2521,(0,0))),((1,4),(2540,(0,0))),((2,-1),(2690,(0,1))),((2,4),(2541,(0,0))),((3,0),(2542,(0,0))),((3,1),(2543,(0,0))),((3,2),(2544,(0,0))),((3,3),(2545,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_731_checked : successorFastRowCheck layer8 row7_731 row7_731choice = true := by decide
def row7_732 : List GridPoint := [(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]
def row7_732choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2617,(1,0))),((0,2),(1996,(0,0))),((0,4),(2423,(0,0))),((1,0),(2503,(0,0))),((1,1),(2515,(0,0))),((1,5),(2547,(0,0))),((2,-1),(2691,(0,1))),((2,3),(2548,(0,0))),((2,4),(2549,(0,0))),((3,0),(2550,(0,0))),((3,1),(2551,(0,0))),((3,2),(2552,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_732_checked : successorFastRowCheck layer8 row7_732 row7_732choice = true := by decide
def row7_733 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_733choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2618,(1,0))),((0,2),(1997,(0,0))),((0,4),(2424,(0,0))),((1,0),(2504,(0,0))),((1,1),(2521,(0,0))),((1,4),(2548,(0,0))),((2,-1),(2692,(0,1))),((2,4),(2555,(0,0))),((3,0),(2556,(0,0))),((3,1),(2557,(0,0))),((3,2),(2558,(0,0))),((3,3),(2559,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_733_checked : successorFastRowCheck layer8 row7_733 row7_733choice = true := by decide
def row7_734 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)]
def row7_734choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2619,(1,0))),((0,2),(1998,(0,0))),((0,4),(2425,(0,0))),((1,0),(2505,(0,0))),((1,1),(2522,(0,0))),((1,4),(2550,(0,0))),((2,-1),(2694,(0,1))),((2,3),(2556,(0,0))),((3,-1),(2697,(0,1))),((3,1),(2560,(0,0))),((3,2),(2561,(0,0))),((4,0),(2562,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_734_checked : successorFastRowCheck layer8 row7_734 row7_734choice = true := by decide
def row7_735 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)]
def row7_735choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2620,(1,0))),((0,2),(1999,(0,0))),((0,4),(2426,(0,0))),((1,0),(2506,(0,0))),((1,1),(2523,(0,0))),((1,4),(2551,(0,0))),((2,-1),(2695,(0,1))),((2,3),(2557,(0,0))),((3,0),(2560,(0,0))),((3,2),(2563,(0,0))),((4,1),(2564,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_735_checked : successorFastRowCheck layer8 row7_735 row7_735choice = true := by decide
def Closure7C091rows : List (List GridPoint) := [row7_728,row7_729,row7_730,row7_731,row7_732,row7_733,row7_734,row7_735]
theorem Closure7C091_closed : ∀ row ∈ Closure7C091rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C091rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_728choice,row7_728_checked⟩
  · subst row
    exact ⟨row7_729choice,row7_729_checked⟩
  · subst row
    exact ⟨row7_730choice,row7_730_checked⟩
  · subst row
    exact ⟨row7_731choice,row7_731_checked⟩
  · subst row
    exact ⟨row7_732choice,row7_732_checked⟩
  · subst row
    exact ⟨row7_733choice,row7_733_checked⟩
  · subst row
    exact ⟨row7_734choice,row7_734_checked⟩
  · subst row
    exact ⟨row7_735choice,row7_735_checked⟩
end Polyomino57
