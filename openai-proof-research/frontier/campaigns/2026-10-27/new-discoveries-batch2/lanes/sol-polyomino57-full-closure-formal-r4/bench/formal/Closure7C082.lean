import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_656 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)]
def row7_656choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2346,(1,0))),((0,1),(1336,(0,0))),((0,3),(1987,(0,0))),((1,0),(2110,(0,0))),((1,3),(2199,(0,0))),((2,-1),(2565,(0,1))),((2,2),(2216,(0,0))),((3,0),(2220,(0,0))),((3,3),(2225,(0,0))),((4,1),(2226,(0,0))),((4,2),(2227,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_656_checked : successorFastRowCheck layer8 row7_656 row7_656choice = true := by decide
def row7_657 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]
def row7_657choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2347,(1,0))),((0,1),(1337,(0,0))),((0,3),(1988,(0,0))),((1,0),(2111,(0,0))),((1,3),(2200,(0,0))),((2,-1),(2566,(0,1))),((2,2),(2217,(0,0))),((3,0),(2222,(0,0))),((3,2),(2226,(0,0))),((4,0),(2228,(0,0))),((4,2),(2229,(0,0))),((5,1),(2230,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_657_checked : successorFastRowCheck layer8 row7_657 row7_657choice = true := by decide
def row7_658 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)]
def row7_658choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2348,(1,0))),((0,1),(1338,(0,0))),((0,3),(1989,(0,0))),((1,0),(2131,(0,0))),((1,3),(2201,(0,0))),((2,0),(2213,(0,0))),((2,3),(2232,(0,0))),((3,-1),(2573,(0,1))),((3,2),(2233,(0,0))),((4,0),(2234,(0,0))),((4,1),(2235,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_658_checked : successorFastRowCheck layer8 row7_658 row7_658choice = true := by decide
def row7_659 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)]
def row7_659choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2349,(1,0))),((0,1),(1339,(0,0))),((0,3),(1990,(0,0))),((1,0),(2136,(0,0))),((1,3),(2203,(0,0))),((2,0),(2220,(0,0))),((2,2),(2233,(0,0))),((3,-1),(2574,(0,1))),((3,3),(2237,(0,0))),((4,0),(2238,(0,0))),((4,1),(2239,(0,0))),((4,2),(2240,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_659_checked : successorFastRowCheck layer8 row7_659 row7_659choice = true := by decide
def row7_660 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)]
def row7_660choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2350,(1,0))),((0,1),(1340,(0,0))),((0,3),(1991,(0,0))),((1,0),(2137,(0,0))),((1,3),(2204,(0,0))),((2,0),(2221,(0,0))),((2,2),(2234,(0,0))),((3,-1),(2576,(0,1))),((3,2),(2238,(0,0))),((4,-1),(2578,(0,1))),((4,1),(2241,(0,0))),((5,0),(2242,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_660_checked : successorFastRowCheck layer8 row7_660 row7_660choice = true := by decide
def row7_661 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]
def row7_661choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2351,(1,0))),((0,1),(1341,(0,0))),((0,3),(1992,(0,0))),((1,0),(2138,(0,0))),((1,3),(2205,(0,0))),((2,0),(2222,(0,0))),((2,2),(2235,(0,0))),((3,-1),(2577,(0,1))),((3,2),(2239,(0,0))),((4,0),(2241,(0,0))),((4,2),(2243,(0,0))),((5,1),(2244,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_661_checked : successorFastRowCheck layer8 row7_661 row7_661choice = true := by decide
def row7_662 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)]
def row7_662choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2352,(1,0))),((0,1),(1342,(0,0))),((0,3),(1993,(0,0))),((1,0),(2142,(0,0))),((1,3),(2206,(0,0))),((2,0),(2228,(0,0))),((2,2),(2236,(0,0))),((3,0),(2241,(0,0))),((3,2),(2245,(0,0))),((4,-1),(2579,(0,1))),((4,2),(2246,(0,0))),((5,0),(2247,(0,0))),((5,1),(2248,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_662_checked : successorFastRowCheck layer8 row7_662 row7_662choice = true := by decide
def row7_663 : List GridPoint := [(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)]
def row7_663choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2353,(1,0))),((0,1),(1343,(0,0))),((0,3),(1994,(0,0))),((1,0),(2154,(0,0))),((1,3),(2207,(0,0))),((2,0),(2231,(0,0))),((2,1),(2233,(0,0))),((2,3),(2250,(0,0))),((3,-1),(2580,(0,1))),((3,3),(2251,(0,0))),((4,0),(2252,(0,0))),((4,1),(2253,(0,0))),((4,2),(2254,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_663_checked : successorFastRowCheck layer8 row7_663 row7_663choice = true := by decide
def Closure7C082rows : List (List GridPoint) := [row7_656,row7_657,row7_658,row7_659,row7_660,row7_661,row7_662,row7_663]
theorem Closure7C082_closed : ∀ row ∈ Closure7C082rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C082rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_656choice,row7_656_checked⟩
  · subst row
    exact ⟨row7_657choice,row7_657_checked⟩
  · subst row
    exact ⟨row7_658choice,row7_658_checked⟩
  · subst row
    exact ⟨row7_659choice,row7_659_checked⟩
  · subst row
    exact ⟨row7_660choice,row7_660_checked⟩
  · subst row
    exact ⟨row7_661choice,row7_661_checked⟩
  · subst row
    exact ⟨row7_662choice,row7_662_checked⟩
  · subst row
    exact ⟨row7_663choice,row7_663_checked⟩
end Polyomino57
