import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_640 : List GridPoint := [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_640choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2330,(1,0))),((0,0),(755,(0,0))),((0,1),(1320,(0,0))),((0,3),(1970,(0,0))),((1,-1),(2499,(0,1))),((1,1),(2104,(0,0))),((1,3),(2165,(0,0))),((2,-1),(2541,(0,1))),((2,4),(2169,(0,0))),((3,0),(2170,(0,0))),((3,1),(2171,(0,0))),((3,2),(2172,(0,0))),((3,3),(2173,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_640_checked : successorFastRowCheck layer8 row7_640 row7_640choice = true := by decide
def row7_641 : List GridPoint := [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_641choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2331,(1,0))),((0,0),(756,(0,0))),((0,1),(1321,(0,0))),((0,3),(1971,(0,0))),((1,-1),(2500,(0,1))),((1,1),(2105,(0,0))),((1,3),(2166,(0,0))),((2,-1),(2543,(0,1))),((2,3),(2170,(0,0))),((3,-1),(2546,(0,1))),((3,1),(2174,(0,0))),((3,2),(2175,(0,0))),((4,0),(2176,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_641_checked : successorFastRowCheck layer8 row7_641 row7_641choice = true := by decide
def row7_642 : List GridPoint := [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_642choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2332,(1,0))),((0,0),(757,(0,0))),((0,1),(1322,(0,0))),((0,3),(1972,(0,0))),((1,-1),(2501,(0,1))),((1,1),(2106,(0,0))),((1,3),(2167,(0,0))),((2,-1),(2544,(0,1))),((2,3),(2171,(0,0))),((3,0),(2174,(0,0))),((3,2),(2177,(0,0))),((4,1),(2178,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_642_checked : successorFastRowCheck layer8 row7_642 row7_642choice = true := by decide
def row7_643 : List GridPoint := [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_643choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2333,(1,0))),((0,0),(758,(0,0))),((0,1),(1323,(0,0))),((0,3),(1973,(0,0))),((1,-1),(2502,(0,1))),((1,1),(2107,(0,0))),((1,3),(2168,(0,0))),((2,-1),(2545,(0,1))),((2,3),(2172,(0,0))),((3,0),(2175,(0,0))),((3,1),(2177,(0,0))),((3,3),(2179,(0,0))),((4,2),(2180,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_643_checked : successorFastRowCheck layer8 row7_643 row7_643choice = true := by decide
def row7_644 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def row7_644choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2334,(1,0))),((0,1),(1324,(0,0))),((0,3),(1975,(0,0))),((0,4),(2044,(0,0))),((1,0),(2054,(0,0))),((1,5),(2182,(0,0))),((2,-1),(2547,(0,1))),((2,2),(2183,(0,0))),((2,3),(2184,(0,0))),((2,4),(2185,(0,0))),((3,0),(2186,(0,0))),((3,1),(2187,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_644_checked : successorFastRowCheck layer8 row7_644 row7_644choice = true := by decide
def row7_645 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row7_645choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2335,(1,0))),((0,1),(1325,(0,0))),((0,3),(1976,(0,0))),((1,0),(2070,(0,0))),((1,4),(2183,(0,0))),((2,-1),(2548,(0,1))),((2,3),(2189,(0,0))),((3,0),(2190,(0,0))),((3,1),(2191,(0,0))),((3,2),(2192,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_645_checked : successorFastRowCheck layer8 row7_645 row7_645choice = true := by decide
def row7_646 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)]
def row7_646choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2336,(1,0))),((0,1),(1326,(0,0))),((0,3),(1977,(0,0))),((1,0),(2071,(0,0))),((1,4),(2184,(0,0))),((2,-1),(2549,(0,1))),((2,2),(2189,(0,0))),((2,4),(2193,(0,0))),((3,0),(2194,(0,0))),((3,1),(2195,(0,0))),((3,3),(2196,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_646_checked : successorFastRowCheck layer8 row7_646 row7_646choice = true := by decide
def row7_647 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]
def row7_647choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2337,(1,0))),((0,1),(1327,(0,0))),((0,3),(1978,(0,0))),((1,0),(2072,(0,0))),((1,4),(2186,(0,0))),((2,-1),(2551,(0,1))),((2,2),(2190,(0,0))),((2,3),(2194,(0,0))),((3,-1),(2553,(0,1))),((3,1),(2197,(0,0))),((4,0),(2198,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_647_checked : successorFastRowCheck layer8 row7_647 row7_647choice = true := by decide
def Closure7C080rows : List (List GridPoint) := [row7_640,row7_641,row7_642,row7_643,row7_644,row7_645,row7_646,row7_647]
theorem Closure7C080_closed : ∀ row ∈ Closure7C080rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C080rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_640choice,row7_640_checked⟩
  · subst row
    exact ⟨row7_641choice,row7_641_checked⟩
  · subst row
    exact ⟨row7_642choice,row7_642_checked⟩
  · subst row
    exact ⟨row7_643choice,row7_643_checked⟩
  · subst row
    exact ⟨row7_644choice,row7_644_checked⟩
  · subst row
    exact ⟨row7_645choice,row7_645_checked⟩
  · subst row
    exact ⟨row7_646choice,row7_646_checked⟩
  · subst row
    exact ⟨row7_647choice,row7_647_checked⟩
end Polyomino57
