import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_752 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_752choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2704,(1,0))),((0,0),(789,(0,0))),((0,1),(1454,(0,0))),((0,2),(2041,(0,0))),((0,3),(2399,(0,0))),((0,5),(2637,(0,0))),((1,-1),(2716,(0,1))),((1,5),(2647,(0,0))),((2,0),(2652,(0,0))),((2,1),(2656,(0,0))),((2,3),(2660,(0,0))),((2,4),(2661,(0,0))),((3,2),(2662,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_752_checked : successorFastRowCheck layer8 row7_752 row7_752choice = true := by decide
def row7_753 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_753choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2705,(1,0))),((0,0),(790,(0,0))),((0,1),(1455,(0,0))),((0,2),(2042,(0,0))),((0,3),(2400,(0,0))),((0,5),(2638,(0,0))),((1,-1),(2717,(0,1))),((1,5),(2648,(0,0))),((2,0),(2653,(0,0))),((2,1),(2657,(0,0))),((2,2),(2660,(0,0))),((2,4),(2663,(0,0))),((3,3),(2664,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_753_checked : successorFastRowCheck layer8 row7_753 row7_753choice = true := by decide
def row7_754 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_754choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2706,(1,0))),((0,0),(791,(0,0))),((0,1),(1456,(0,0))),((0,2),(2043,(0,0))),((0,3),(2401,(0,0))),((0,5),(2639,(0,0))),((1,-1),(2718,(0,1))),((1,5),(2649,(0,0))),((2,0),(2654,(0,0))),((2,1),(2658,(0,0))),((2,2),(2661,(0,0))),((2,3),(2663,(0,0))),((2,5),(2665,(0,0))),((3,4),(2666,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_754_checked : successorFastRowCheck layer8 row7_754 row7_754choice = true := by decide
def row7_755 : List GridPoint := [(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def row7_755choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2707,(1,0))),((0,1),(1457,(0,0))),((0,2),(2044,(0,0))),((0,3),(2416,(0,0))),((0,5),(2640,(0,0))),((1,0),(2651,(0,0))),((1,5),(2673,(0,0))),((2,-1),(2720,(0,1))),((2,2),(2674,(0,0))),((2,3),(2675,(0,0))),((2,4),(2676,(0,0))),((3,0),(2677,(0,0))),((3,1),(2678,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_755_checked : successorFastRowCheck layer8 row7_755 row7_755choice = true := by decide
def row7_756 : List GridPoint := [(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]
def row7_756choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2708,(1,0))),((0,2),(2045,(0,0))),((0,3),(2423,(0,0))),((0,5),(2641,(0,0))),((1,0),(2670,(0,0))),((1,1),(2674,(0,0))),((1,5),(2682,(0,0))),((2,-1),(2721,(0,1))),((2,3),(2683,(0,0))),((2,4),(2684,(0,0))),((3,0),(2685,(0,0))),((3,1),(2686,(0,0))),((3,2),(2687,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_756_checked : successorFastRowCheck layer8 row7_756 row7_756choice = true := by decide
def row7_757 : List GridPoint := [(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)]
def row7_757choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2709,(1,0))),((0,3),(2430,(0,0))),((0,5),(2642,(0,0))),((1,0),(2671,(0,0))),((1,1),(2680,(0,0))),((1,2),(2683,(0,0))),((1,5),(2691,(0,0))),((2,-1),(2722,(0,1))),((2,4),(2692,(0,0))),((3,0),(2693,(0,0))),((3,1),(2694,(0,0))),((3,2),(2695,(0,0))),((3,3),(2696,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_757_checked : successorFastRowCheck layer8 row7_757 row7_757choice = true := by decide
def row7_758 : List GridPoint := [(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)]
def row7_758choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(2710,(1,0))),((0,3),(2439,(0,0))),((0,5),(2643,(0,0))),((1,0),(2672,(0,0))),((1,1),(2681,(0,0))),((1,2),(2690,(0,0))),((1,3),(2692,(0,0))),((1,5),(2700,(0,0))),((2,-1),(2723,(0,1))),((2,5),(2701,(0,0))),((3,0),(2702,(0,0))),((3,1),(2703,(0,0))),((3,2),(2704,(0,0))),((3,3),(2705,(0,0))),((3,4),(2706,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_758_checked : successorFastRowCheck layer8 row7_758 row7_758choice = true := by decide
def row7_759 : List GridPoint := [(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_759choice (b : GridPoint) : ℕ × GridPoint := (([((-1,5),(2723,(1,0))),((0,0),(792,(0,0))),((0,1),(1458,(0,0))),((0,2),(2046,(0,0))),((0,3),(2440,(0,0))),((0,4),(2634,(0,0))),((0,6),(2711,(0,0))),((1,-1),(2724,(0,1))),((1,6),(2712,(0,0))),((2,0),(2713,(0,0))),((2,1),(2714,(0,0))),((2,2),(2715,(0,0))),((2,3),(2716,(0,0))),((2,4),(2717,(0,0))),((2,5),(2718,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_759_checked : successorFastRowCheck layer8 row7_759 row7_759choice = true := by decide
def Closure7C094rows : List (List GridPoint) := [row7_752,row7_753,row7_754,row7_755,row7_756,row7_757,row7_758,row7_759]
theorem Closure7C094_closed : ∀ row ∈ Closure7C094rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C094rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_752choice,row7_752_checked⟩
  · subst row
    exact ⟨row7_753choice,row7_753_checked⟩
  · subst row
    exact ⟨row7_754choice,row7_754_checked⟩
  · subst row
    exact ⟨row7_755choice,row7_755_checked⟩
  · subst row
    exact ⟨row7_756choice,row7_756_checked⟩
  · subst row
    exact ⟨row7_757choice,row7_757_checked⟩
  · subst row
    exact ⟨row7_758choice,row7_758_checked⟩
  · subst row
    exact ⟨row7_759choice,row7_759_checked⟩
end Polyomino57
