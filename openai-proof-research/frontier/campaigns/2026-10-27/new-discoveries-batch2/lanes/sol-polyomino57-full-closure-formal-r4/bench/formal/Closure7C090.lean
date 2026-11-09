import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_720 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def row7_720choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2605,(1,0))),((0,0),(780,(0,0))),((0,1),(1440,(0,0))),((0,2),(1946,(0,0))),((0,4),(2411,(0,0))),((1,-1),(2665,(0,1))),((1,4),(2460,(0,0))),((2,0),(2471,(0,0))),((2,1),(2479,(0,0))),((2,2),(2485,(0,0))),((2,5),(2491,(0,0))),((3,3),(2492,(0,0))),((3,4),(2493,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_720_checked : successorFastRowCheck layer8 row7_720 row7_720choice = true := by decide
def row7_721 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def row7_721choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2606,(1,0))),((0,0),(781,(0,0))),((0,1),(1441,(0,0))),((0,2),(1947,(0,0))),((0,4),(2412,(0,0))),((1,-1),(2666,(0,1))),((1,4),(2461,(0,0))),((2,0),(2473,(0,0))),((2,1),(2481,(0,0))),((2,2),(2487,(0,0))),((2,4),(2492,(0,0))),((3,2),(2494,(0,0))),((3,4),(2495,(0,0))),((4,3),(2496,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_721_checked : successorFastRowCheck layer8 row7_721 row7_721choice = true := by decide
def row7_722 : List GridPoint := [(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def row7_722choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2607,(1,0))),((0,0),(782,(0,0))),((0,1),(1442,(0,0))),((0,2),(1968,(0,0))),((0,4),(2413,(0,0))),((1,-1),(2667,(0,1))),((1,2),(2476,(0,0))),((1,4),(2497,(0,0))),((2,0),(2498,(0,0))),((2,4),(2499,(0,0))),((3,1),(2500,(0,0))),((3,2),(2501,(0,0))),((3,3),(2502,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_722_checked : successorFastRowCheck layer8 row7_722 row7_722choice = true := by decide
def row7_723 : List GridPoint := [(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_723choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2608,(1,0))),((0,0),(783,(0,0))),((0,2),(1969,(0,0))),((0,4),(2414,(0,0))),((1,-1),(2668,(0,1))),((1,1),(2464,(0,0))),((1,4),(2503,(0,0))),((2,-1),(2680,(0,1))),((2,3),(2504,(0,0))),((3,0),(2505,(0,0))),((3,1),(2506,(0,0))),((3,2),(2507,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_723_checked : successorFastRowCheck layer8 row7_723 row7_723choice = true := by decide
def row7_724 : List GridPoint := [(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)]
def row7_724choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2609,(1,0))),((0,0),(784,(0,0))),((0,2),(1974,(0,0))),((0,4),(2415,(0,0))),((1,-1),(2669,(0,1))),((1,1),(2498,(0,0))),((1,2),(2504,(0,0))),((1,4),(2508,(0,0))),((2,-1),(2681,(0,1))),((2,4),(2509,(0,0))),((3,0),(2510,(0,0))),((3,1),(2511,(0,0))),((3,2),(2512,(0,0))),((3,3),(2513,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_724_checked : successorFastRowCheck layer8 row7_724 row7_724choice = true := by decide
def row7_725 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def row7_725choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2610,(1,0))),((0,1),(1443,(0,0))),((0,2),(1975,(0,0))),((0,4),(2416,(0,0))),((1,0),(2448,(0,0))),((1,5),(2514,(0,0))),((2,-1),(2682,(0,1))),((2,2),(2515,(0,0))),((2,3),(2516,(0,0))),((2,4),(2517,(0,0))),((3,0),(2518,(0,0))),((3,1),(2519,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_725_checked : successorFastRowCheck layer8 row7_725 row7_725choice = true := by decide
def row7_726 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_726choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2611,(1,0))),((0,1),(1444,(0,0))),((0,2),(1976,(0,0))),((0,4),(2417,(0,0))),((1,0),(2464,(0,0))),((1,4),(2515,(0,0))),((2,-1),(2683,(0,1))),((2,3),(2521,(0,0))),((3,0),(2522,(0,0))),((3,1),(2523,(0,0))),((3,2),(2524,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_726_checked : successorFastRowCheck layer8 row7_726 row7_726choice = true := by decide
def row7_727 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)]
def row7_727choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(2612,(1,0))),((0,1),(1445,(0,0))),((0,2),(1977,(0,0))),((0,4),(2418,(0,0))),((1,0),(2465,(0,0))),((1,4),(2516,(0,0))),((2,-1),(2684,(0,1))),((2,2),(2521,(0,0))),((2,4),(2525,(0,0))),((3,0),(2526,(0,0))),((3,1),(2527,(0,0))),((3,3),(2528,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_727_checked : successorFastRowCheck layer8 row7_727 row7_727choice = true := by decide
def Closure7C090rows : List (List GridPoint) := [row7_720,row7_721,row7_722,row7_723,row7_724,row7_725,row7_726,row7_727]
theorem Closure7C090_closed : ∀ row ∈ Closure7C090rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C090rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_720choice,row7_720_checked⟩
  · subst row
    exact ⟨row7_721choice,row7_721_checked⟩
  · subst row
    exact ⟨row7_722choice,row7_722_checked⟩
  · subst row
    exact ⟨row7_723choice,row7_723_checked⟩
  · subst row
    exact ⟨row7_724choice,row7_724_checked⟩
  · subst row
    exact ⟨row7_725choice,row7_725_checked⟩
  · subst row
    exact ⟨row7_726choice,row7_726_checked⟩
  · subst row
    exact ⟨row7_727choice,row7_727_checked⟩
end Polyomino57
