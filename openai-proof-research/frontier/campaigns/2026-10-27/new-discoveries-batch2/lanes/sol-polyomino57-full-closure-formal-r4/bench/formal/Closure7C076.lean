import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_608 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_608choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2298,(1,0))),((0,0),(723,(0,0))),((0,1),(1256,(0,0))),((0,3),(1937,(0,0))),((1,-1),(2453,(0,1))),((1,4),(2054,(0,0))),((2,-1),(2515,(0,1))),((2,2),(2070,(0,0))),((2,3),(2071,(0,0))),((3,0),(2072,(0,0))),((3,1),(2073,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_608_checked : successorFastRowCheck layer8 row7_608 row7_608choice = true := by decide
def row7_609 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def row7_609choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2299,(1,0))),((0,0),(724,(0,0))),((0,1),(1257,(0,0))),((0,3),(1938,(0,0))),((1,-1),(2454,(0,1))),((1,4),(2055,(0,0))),((2,-1),(2516,(0,1))),((2,1),(2070,(0,0))),((2,3),(2074,(0,0))),((3,0),(2075,(0,0))),((3,2),(2076,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_609_checked : successorFastRowCheck layer8 row7_609 row7_609choice = true := by decide
def row7_610 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def row7_610choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2300,(1,0))),((0,0),(725,(0,0))),((0,1),(1258,(0,0))),((0,3),(1939,(0,0))),((1,-1),(2455,(0,1))),((1,4),(2056,(0,0))),((2,-1),(2517,(0,1))),((2,1),(2071,(0,0))),((2,2),(2074,(0,0))),((2,4),(2077,(0,0))),((3,0),(2078,(0,0))),((3,3),(2079,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_610_checked : successorFastRowCheck layer8 row7_610 row7_610choice = true := by decide
def row7_611 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def row7_611choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2301,(1,0))),((0,0),(726,(0,0))),((0,1),(1259,(0,0))),((0,3),(1940,(0,0))),((1,-1),(2456,(0,1))),((1,4),(2058,(0,0))),((2,-1),(2519,(0,1))),((2,1),(2072,(0,0))),((2,2),(2075,(0,0))),((2,3),(2078,(0,0))),((3,-1),(2520,(0,1))),((3,1),(2080,(0,0))),((4,0),(2081,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_611_checked : successorFastRowCheck layer8 row7_611 row7_611choice = true := by decide
def row7_612 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def row7_612choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2302,(1,0))),((0,0),(727,(0,0))),((0,1),(1260,(0,0))),((0,3),(1941,(0,0))),((1,-1),(2457,(0,1))),((1,4),(2059,(0,0))),((2,0),(2070,(0,0))),((2,3),(2082,(0,0))),((3,1),(2083,(0,0))),((3,2),(2084,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_612_checked : successorFastRowCheck layer8 row7_612 row7_612choice = true := by decide
def row7_613 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def row7_613choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2303,(1,0))),((0,0),(728,(0,0))),((0,1),(1261,(0,0))),((0,3),(1942,(0,0))),((1,-1),(2458,(0,1))),((1,4),(2060,(0,0))),((2,0),(2071,(0,0))),((2,2),(2082,(0,0))),((2,4),(2085,(0,0))),((3,1),(2086,(0,0))),((3,3),(2087,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_613_checked : successorFastRowCheck layer8 row7_613 row7_613choice = true := by decide
def row7_614 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def row7_614choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2304,(1,0))),((0,0),(729,(0,0))),((0,1),(1262,(0,0))),((0,3),(1943,(0,0))),((1,-1),(2459,(0,1))),((1,4),(2062,(0,0))),((2,0),(2073,(0,0))),((2,2),(2083,(0,0))),((2,3),(2086,(0,0))),((3,0),(2088,(0,0))),((3,2),(2089,(0,0))),((4,1),(2090,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_614_checked : successorFastRowCheck layer8 row7_614 row7_614choice = true := by decide
def row7_615 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def row7_615choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2305,(1,0))),((0,0),(730,(0,0))),((0,1),(1263,(0,0))),((0,3),(1944,(0,0))),((1,-1),(2460,(0,1))),((1,4),(2063,(0,0))),((2,0),(2074,(0,0))),((2,1),(2082,(0,0))),((2,4),(2091,(0,0))),((3,2),(2092,(0,0))),((3,3),(2093,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_615_checked : successorFastRowCheck layer8 row7_615 row7_615choice = true := by decide
def Closure7C076rows : List (List GridPoint) := [row7_608,row7_609,row7_610,row7_611,row7_612,row7_613,row7_614,row7_615]
theorem Closure7C076_closed : ∀ row ∈ Closure7C076rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C076rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_608choice,row7_608_checked⟩
  · subst row
    exact ⟨row7_609choice,row7_609_checked⟩
  · subst row
    exact ⟨row7_610choice,row7_610_checked⟩
  · subst row
    exact ⟨row7_611choice,row7_611_checked⟩
  · subst row
    exact ⟨row7_612choice,row7_612_checked⟩
  · subst row
    exact ⟨row7_613choice,row7_613_checked⟩
  · subst row
    exact ⟨row7_614choice,row7_614_checked⟩
  · subst row
    exact ⟨row7_615choice,row7_615_checked⟩
end Polyomino57
