import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_672 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)]
def row7_672choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2362,(1,0))),((0,1),(1394,(0,0))),((0,3),(2004,(0,0))),((1,0),(2170,(0,0))),((1,1),(2209,(0,0))),((1,3),(2266,(0,0))),((2,-1),(2592,(0,1))),((2,4),(2293,(0,0))),((3,-1),(2610,(0,1))),((3,1),(2298,(0,0))),((3,2),(2299,(0,0))),((3,3),(2300,(0,0))),((4,0),(2301,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_672_checked : successorFastRowCheck layer8 row7_672 row7_672choice = true := by decide
def row7_673 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)]
def row7_673choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2363,(1,0))),((0,1),(1395,(0,0))),((0,3),(2005,(0,0))),((1,0),(2171,(0,0))),((1,1),(2210,(0,0))),((1,3),(2267,(0,0))),((2,-1),(2593,(0,1))),((2,4),(2294,(0,0))),((3,0),(2298,(0,0))),((3,2),(2302,(0,0))),((3,3),(2303,(0,0))),((4,1),(2304,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_673_checked : successorFastRowCheck layer8 row7_673 row7_673choice = true := by decide
def row7_674 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)]
def row7_674choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2364,(1,0))),((0,1),(1396,(0,0))),((0,3),(2006,(0,0))),((1,0),(2172,(0,0))),((1,1),(2211,(0,0))),((1,3),(2268,(0,0))),((2,-1),(2594,(0,1))),((2,4),(2295,(0,0))),((3,0),(2299,(0,0))),((3,1),(2302,(0,0))),((3,3),(2305,(0,0))),((4,2),(2306,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_674_checked : successorFastRowCheck layer8 row7_674 row7_674choice = true := by decide
def row7_675 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]
def row7_675choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2365,(1,0))),((0,1),(1397,(0,0))),((0,3),(2007,(0,0))),((1,0),(2173,(0,0))),((1,1),(2212,(0,0))),((1,3),(2269,(0,0))),((2,-1),(2595,(0,1))),((2,4),(2296,(0,0))),((3,0),(2300,(0,0))),((3,1),(2303,(0,0))),((3,2),(2305,(0,0))),((3,4),(2307,(0,0))),((4,3),(2308,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_675_checked : successorFastRowCheck layer8 row7_675 row7_675choice = true := by decide
def row7_676 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)]
def row7_676choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2366,(1,0))),((0,1),(1398,(0,0))),((0,3),(2008,(0,0))),((1,0),(2174,(0,0))),((1,1),(2213,(0,0))),((1,3),(2270,(0,0))),((2,-1),(2600,(0,1))),((2,3),(2298,(0,0))),((3,-1),(2611,(0,1))),((3,2),(2309,(0,0))),((4,0),(2310,(0,0))),((4,1),(2311,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_676_checked : successorFastRowCheck layer8 row7_676 row7_676choice = true := by decide
def row7_677 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)]
def row7_677choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2367,(1,0))),((0,1),(1399,(0,0))),((0,3),(2009,(0,0))),((1,0),(2175,(0,0))),((1,1),(2214,(0,0))),((1,3),(2271,(0,0))),((2,-1),(2601,(0,1))),((2,3),(2299,(0,0))),((3,-1),(2612,(0,1))),((3,1),(2309,(0,0))),((3,3),(2312,(0,0))),((4,0),(2313,(0,0))),((4,2),(2314,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_677_checked : successorFastRowCheck layer8 row7_677 row7_677choice = true := by decide
def row7_678 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]
def row7_678choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2368,(1,0))),((0,1),(1400,(0,0))),((0,3),(2010,(0,0))),((1,0),(2176,(0,0))),((1,1),(2215,(0,0))),((1,3),(2272,(0,0))),((2,-1),(2602,(0,1))),((2,3),(2301,(0,0))),((3,-1),(2614,(0,1))),((3,1),(2310,(0,0))),((3,2),(2313,(0,0))),((4,-1),(2615,(0,1))),((4,1),(2315,(0,0))),((5,0),(2316,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_678_checked : successorFastRowCheck layer8 row7_678 row7_678choice = true := by decide
def row7_679 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)]
def row7_679choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2369,(1,0))),((0,1),(1401,(0,0))),((0,3),(2011,(0,0))),((1,0),(2177,(0,0))),((1,1),(2216,(0,0))),((1,3),(2273,(0,0))),((2,-1),(2603,(0,1))),((2,3),(2302,(0,0))),((3,0),(2309,(0,0))),((3,3),(2317,(0,0))),((4,1),(2318,(0,0))),((4,2),(2319,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_679_checked : successorFastRowCheck layer8 row7_679 row7_679choice = true := by decide
def Closure7C084rows : List (List GridPoint) := [row7_672,row7_673,row7_674,row7_675,row7_676,row7_677,row7_678,row7_679]
theorem Closure7C084_closed : ∀ row ∈ Closure7C084rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C084rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_672choice,row7_672_checked⟩
  · subst row
    exact ⟨row7_673choice,row7_673_checked⟩
  · subst row
    exact ⟨row7_674choice,row7_674_checked⟩
  · subst row
    exact ⟨row7_675choice,row7_675_checked⟩
  · subst row
    exact ⟨row7_676choice,row7_676_checked⟩
  · subst row
    exact ⟨row7_677choice,row7_677_checked⟩
  · subst row
    exact ⟨row7_678choice,row7_678_checked⟩
  · subst row
    exact ⟨row7_679choice,row7_679_checked⟩
end Polyomino57
