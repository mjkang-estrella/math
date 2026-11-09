import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_648 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]
def row7_648choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2338,(1,0))),((0,1),(1328,(0,0))),((0,3),(1979,(0,0))),((1,0),(2073,(0,0))),((1,4),(2187,(0,0))),((2,-1),(2552,(0,1))),((2,2),(2191,(0,0))),((2,3),(2195,(0,0))),((3,0),(2197,(0,0))),((3,2),(2199,(0,0))),((4,1),(2200,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_648_checked : successorFastRowCheck layer8 row7_648 row7_648choice = true := by decide
def row7_649 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]
def row7_649choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2339,(1,0))),((0,1),(1329,(0,0))),((0,3),(1980,(0,0))),((1,0),(2088,(0,0))),((1,4),(2188,(0,0))),((2,0),(2197,(0,0))),((2,2),(2201,(0,0))),((2,3),(2202,(0,0))),((3,-1),(2554,(0,1))),((3,2),(2203,(0,0))),((4,0),(2204,(0,0))),((4,1),(2205,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_649_checked : successorFastRowCheck layer8 row7_649 row7_649choice = true := by decide
def row7_650 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row7_650choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2340,(1,0))),((0,1),(1330,(0,0))),((0,3),(1981,(0,0))),((1,0),(2104,(0,0))),((1,3),(2189,(0,0))),((2,-1),(2555,(0,1))),((2,4),(2208,(0,0))),((3,0),(2209,(0,0))),((3,1),(2210,(0,0))),((3,2),(2211,(0,0))),((3,3),(2212,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_650_checked : successorFastRowCheck layer8 row7_650 row7_650choice = true := by decide
def row7_651 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row7_651choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2341,(1,0))),((0,1),(1331,(0,0))),((0,3),(1982,(0,0))),((1,0),(2105,(0,0))),((1,3),(2190,(0,0))),((2,-1),(2557,(0,1))),((2,3),(2209,(0,0))),((3,-1),(2568,(0,1))),((3,1),(2213,(0,0))),((3,2),(2214,(0,0))),((4,0),(2215,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_651_checked : successorFastRowCheck layer8 row7_651 row7_651choice = true := by decide
def row7_652 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row7_652choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2342,(1,0))),((0,1),(1332,(0,0))),((0,3),(1983,(0,0))),((1,0),(2106,(0,0))),((1,3),(2191,(0,0))),((2,-1),(2558,(0,1))),((2,3),(2210,(0,0))),((3,0),(2213,(0,0))),((3,2),(2216,(0,0))),((4,1),(2217,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_652_checked : successorFastRowCheck layer8 row7_652 row7_652choice = true := by decide
def row7_653 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row7_653choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2343,(1,0))),((0,1),(1333,(0,0))),((0,3),(1984,(0,0))),((1,0),(2107,(0,0))),((1,3),(2192,(0,0))),((2,-1),(2559,(0,1))),((2,3),(2211,(0,0))),((3,0),(2214,(0,0))),((3,1),(2216,(0,0))),((3,3),(2218,(0,0))),((4,2),(2219,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_653_checked : successorFastRowCheck layer8 row7_653 row7_653choice = true := by decide
def row7_654 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)]
def row7_654choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2344,(1,0))),((0,1),(1334,(0,0))),((0,3),(1985,(0,0))),((1,0),(2108,(0,0))),((1,3),(2197,(0,0))),((2,-1),(2563,(0,1))),((2,2),(2213,(0,0))),((3,-1),(2569,(0,1))),((3,2),(2220,(0,0))),((4,0),(2221,(0,0))),((4,1),(2222,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_654_checked : successorFastRowCheck layer8 row7_654 row7_654choice = true := by decide
def row7_655 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]
def row7_655choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2345,(1,0))),((0,1),(1335,(0,0))),((0,3),(1986,(0,0))),((1,0),(2109,(0,0))),((1,3),(2198,(0,0))),((2,-1),(2564,(0,1))),((2,2),(2215,(0,0))),((3,-1),(2571,(0,1))),((3,1),(2221,(0,0))),((4,-1),(2572,(0,1))),((4,1),(2223,(0,0))),((5,0),(2224,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_655_checked : successorFastRowCheck layer8 row7_655 row7_655choice = true := by decide
def Closure7C081rows : List (List GridPoint) := [row7_648,row7_649,row7_650,row7_651,row7_652,row7_653,row7_654,row7_655]
theorem Closure7C081_closed : ∀ row ∈ Closure7C081rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C081rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_648choice,row7_648_checked⟩
  · subst row
    exact ⟨row7_649choice,row7_649_checked⟩
  · subst row
    exact ⟨row7_650choice,row7_650_checked⟩
  · subst row
    exact ⟨row7_651choice,row7_651_checked⟩
  · subst row
    exact ⟨row7_652choice,row7_652_checked⟩
  · subst row
    exact ⟨row7_653choice,row7_653_checked⟩
  · subst row
    exact ⟨row7_654choice,row7_654_checked⟩
  · subst row
    exact ⟨row7_655choice,row7_655_checked⟩
end Polyomino57
