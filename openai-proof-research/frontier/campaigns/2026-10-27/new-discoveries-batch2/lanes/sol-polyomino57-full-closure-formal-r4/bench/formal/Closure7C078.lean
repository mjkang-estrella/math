import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_624 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def row7_624choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2314,(1,0))),((0,0),(739,(0,0))),((0,1),(1272,(0,0))),((0,3),(1953,(0,0))),((1,-1),(2481,(0,1))),((1,3),(2076,(0,0))),((2,-1),(2528,(0,1))),((2,1),(2107,(0,0))),((2,3),(2114,(0,0))),((3,0),(2117,(0,0))),((3,1),(2119,(0,0))),((3,3),(2120,(0,0))),((4,2),(2121,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_624_checked : successorFastRowCheck layer8 row7_624 row7_624choice = true := by decide
def row7_625 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def row7_625choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2315,(1,0))),((0,0),(740,(0,0))),((0,1),(1273,(0,0))),((0,3),(1954,(0,0))),((1,-1),(2483,(0,1))),((1,3),(2080,(0,0))),((2,-1),(2531,(0,1))),((2,1),(2108,(0,0))),((2,2),(2116,(0,0))),((3,-1),(2535,(0,1))),((3,2),(2122,(0,0))),((4,0),(2123,(0,0))),((4,1),(2124,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_625_checked : successorFastRowCheck layer8 row7_625 row7_625choice = true := by decide
def row7_626 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def row7_626choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2316,(1,0))),((0,0),(741,(0,0))),((0,1),(1274,(0,0))),((0,3),(1955,(0,0))),((1,-1),(2484,(0,1))),((1,3),(2081,(0,0))),((2,-1),(2532,(0,1))),((2,1),(2109,(0,0))),((2,2),(2118,(0,0))),((3,-1),(2537,(0,1))),((3,1),(2123,(0,0))),((4,-1),(2538,(0,1))),((4,1),(2125,(0,0))),((5,0),(2126,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_626_checked : successorFastRowCheck layer8 row7_626 row7_626choice = true := by decide
def row7_627 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def row7_627choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2317,(1,0))),((0,0),(742,(0,0))),((0,1),(1275,(0,0))),((0,3),(1956,(0,0))),((1,-1),(2485,(0,1))),((1,3),(2082,(0,0))),((2,0),(2104,(0,0))),((2,4),(2127,(0,0))),((3,1),(2128,(0,0))),((3,2),(2129,(0,0))),((3,3),(2130,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_627_checked : successorFastRowCheck layer8 row7_627 row7_627choice = true := by decide
def row7_628 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def row7_628choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2318,(1,0))),((0,0),(743,(0,0))),((0,1),(1276,(0,0))),((0,3),(1957,(0,0))),((1,-1),(2486,(0,1))),((1,3),(2083,(0,0))),((2,0),(2106,(0,0))),((2,3),(2128,(0,0))),((3,0),(2131,(0,0))),((3,2),(2132,(0,0))),((4,1),(2133,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_628_checked : successorFastRowCheck layer8 row7_628 row7_628choice = true := by decide
def row7_629 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def row7_629choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2319,(1,0))),((0,0),(744,(0,0))),((0,1),(1277,(0,0))),((0,3),(1958,(0,0))),((1,-1),(2487,(0,1))),((1,3),(2084,(0,0))),((2,0),(2107,(0,0))),((2,3),(2129,(0,0))),((3,1),(2132,(0,0))),((3,3),(2134,(0,0))),((4,2),(2135,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_629_checked : successorFastRowCheck layer8 row7_629 row7_629choice = true := by decide
def row7_630 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_630choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2320,(1,0))),((0,0),(745,(0,0))),((0,1),(1278,(0,0))),((0,3),(1959,(0,0))),((1,-1),(2488,(0,1))),((1,3),(2088,(0,0))),((2,0),(2108,(0,0))),((2,2),(2131,(0,0))),((3,-1),(2539,(0,1))),((3,2),(2136,(0,0))),((4,0),(2137,(0,0))),((4,1),(2138,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_630_checked : successorFastRowCheck layer8 row7_630 row7_630choice = true := by decide
def row7_631 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def row7_631choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2321,(1,0))),((0,0),(746,(0,0))),((0,1),(1279,(0,0))),((0,3),(1960,(0,0))),((1,-1),(2489,(0,1))),((1,3),(2089,(0,0))),((2,0),(2110,(0,0))),((2,2),(2132,(0,0))),((3,0),(2136,(0,0))),((3,3),(2139,(0,0))),((4,1),(2140,(0,0))),((4,2),(2141,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_631_checked : successorFastRowCheck layer8 row7_631 row7_631choice = true := by decide
def Closure7C078rows : List (List GridPoint) := [row7_624,row7_625,row7_626,row7_627,row7_628,row7_629,row7_630,row7_631]
theorem Closure7C078_closed : ∀ row ∈ Closure7C078rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C078rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_624choice,row7_624_checked⟩
  · subst row
    exact ⟨row7_625choice,row7_625_checked⟩
  · subst row
    exact ⟨row7_626choice,row7_626_checked⟩
  · subst row
    exact ⟨row7_627choice,row7_627_checked⟩
  · subst row
    exact ⟨row7_628choice,row7_628_checked⟩
  · subst row
    exact ⟨row7_629choice,row7_629_checked⟩
  · subst row
    exact ⟨row7_630choice,row7_630_checked⟩
  · subst row
    exact ⟨row7_631choice,row7_631_checked⟩
end Polyomino57
