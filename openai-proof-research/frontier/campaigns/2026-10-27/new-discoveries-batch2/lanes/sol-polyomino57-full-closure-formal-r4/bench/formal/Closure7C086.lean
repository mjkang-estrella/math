import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_688 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)]
def row7_688choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2378,(1,0))),((0,1),(1410,(0,0))),((0,3),(2020,(0,0))),((1,1),(2236,(0,0))),((1,3),(2282,(0,0))),((2,0),(2320,(0,0))),((2,3),(2339,(0,0))),((3,0),(2344,(0,0))),((3,2),(2348,(0,0))),((4,-1),(2623,(0,1))),((4,2),(2349,(0,0))),((5,0),(2350,(0,0))),((5,1),(2351,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_688_checked : successorFastRowCheck layer8 row7_688 row7_688choice = true := by decide
def row7_689 : List GridPoint := [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)]
def row7_689choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2379,(1,0))),((0,1),(1411,(0,0))),((0,3),(2021,(0,0))),((1,1),(2250,(0,0))),((1,3),(2283,(0,0))),((2,0),(2329,(0,0))),((2,1),(2335,(0,0))),((2,4),(2354,(0,0))),((3,-1),(2624,(0,1))),((3,3),(2355,(0,0))),((4,0),(2356,(0,0))),((4,1),(2357,(0,0))),((4,2),(2358,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_689_checked : successorFastRowCheck layer8 row7_689 row7_689choice = true := by decide
def row7_690 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)]
def row7_690choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2380,(1,0))),((0,1),(1412,(0,0))),((0,3),(2022,(0,0))),((1,1),(2251,(0,0))),((1,3),(2284,(0,0))),((2,0),(2330,(0,0))),((2,1),(2340,(0,0))),((2,3),(2355,(0,0))),((3,-1),(2625,(0,1))),((3,4),(2361,(0,0))),((4,0),(2362,(0,0))),((4,1),(2363,(0,0))),((4,2),(2364,(0,0))),((4,3),(2365,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_690_checked : successorFastRowCheck layer8 row7_690 row7_690choice = true := by decide
def row7_691 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)]
def row7_691choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2381,(1,0))),((0,1),(1413,(0,0))),((0,3),(2023,(0,0))),((1,1),(2252,(0,0))),((1,3),(2285,(0,0))),((2,0),(2331,(0,0))),((2,1),(2341,(0,0))),((2,3),(2356,(0,0))),((3,-1),(2627,(0,1))),((3,3),(2362,(0,0))),((4,-1),(2630,(0,1))),((4,1),(2366,(0,0))),((4,2),(2367,(0,0))),((5,0),(2368,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_691_checked : successorFastRowCheck layer8 row7_691 row7_691choice = true := by decide
def row7_692 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)]
def row7_692choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2382,(1,0))),((0,1),(1414,(0,0))),((0,3),(2024,(0,0))),((1,1),(2253,(0,0))),((1,3),(2286,(0,0))),((2,0),(2332,(0,0))),((2,1),(2342,(0,0))),((2,3),(2357,(0,0))),((3,-1),(2628,(0,1))),((3,3),(2363,(0,0))),((4,0),(2366,(0,0))),((4,2),(2369,(0,0))),((5,1),(2370,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_692_checked : successorFastRowCheck layer8 row7_692 row7_692choice = true := by decide
def row7_693 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]
def row7_693choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2383,(1,0))),((0,1),(1415,(0,0))),((0,3),(2025,(0,0))),((1,1),(2254,(0,0))),((1,3),(2287,(0,0))),((2,0),(2333,(0,0))),((2,1),(2343,(0,0))),((2,3),(2358,(0,0))),((3,-1),(2629,(0,1))),((3,3),(2364,(0,0))),((4,0),(2367,(0,0))),((4,1),(2369,(0,0))),((4,3),(2371,(0,0))),((5,2),(2372,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_693_checked : successorFastRowCheck layer8 row7_693 row7_693choice = true := by decide
def row7_694 : List GridPoint := [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)]
def row7_694choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2384,(1,0))),((0,1),(1416,(0,0))),((0,3),(2026,(0,0))),((1,1),(2255,(0,0))),((1,3),(2288,(0,0))),((2,1),(2348,(0,0))),((2,3),(2359,(0,0))),((3,0),(2366,(0,0))),((3,3),(2374,(0,0))),((4,-1),(2631,(0,1))),((4,2),(2375,(0,0))),((5,0),(2376,(0,0))),((5,1),(2377,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_694_checked : successorFastRowCheck layer8 row7_694 row7_694choice = true := by decide
def row7_695 : List GridPoint := [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)]
def row7_695choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(2385,(1,0))),((0,1),(1417,(0,0))),((0,3),(2027,(0,0))),((1,1),(2256,(0,0))),((1,3),(2289,(0,0))),((2,1),(2353,(0,0))),((2,3),(2360,(0,0))),((3,0),(2373,(0,0))),((3,1),(2375,(0,0))),((3,3),(2379,(0,0))),((4,-1),(2632,(0,1))),((4,3),(2380,(0,0))),((5,0),(2381,(0,0))),((5,1),(2382,(0,0))),((5,2),(2383,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_695_checked : successorFastRowCheck layer8 row7_695 row7_695choice = true := by decide
def Closure7C086rows : List (List GridPoint) := [row7_688,row7_689,row7_690,row7_691,row7_692,row7_693,row7_694,row7_695]
theorem Closure7C086_closed : ∀ row ∈ Closure7C086rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C086rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_688choice,row7_688_checked⟩
  · subst row
    exact ⟨row7_689choice,row7_689_checked⟩
  · subst row
    exact ⟨row7_690choice,row7_690_checked⟩
  · subst row
    exact ⟨row7_691choice,row7_691_checked⟩
  · subst row
    exact ⟨row7_692choice,row7_692_checked⟩
  · subst row
    exact ⟨row7_693choice,row7_693_checked⟩
  · subst row
    exact ⟨row7_694choice,row7_694_checked⟩
  · subst row
    exact ⟨row7_695choice,row7_695_checked⟩
end Polyomino57
