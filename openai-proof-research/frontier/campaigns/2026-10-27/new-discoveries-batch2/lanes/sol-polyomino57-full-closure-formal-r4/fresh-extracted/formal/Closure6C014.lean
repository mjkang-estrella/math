import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_112 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1)]
def row6_112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(505,(1,0))),((-1,2),(644,(1,0))),((-1,3),(725,(1,0))),((-1,4),(755,(1,0))),((0,0),(7,(0,0))),((0,5),(353,(0,0))),((1,-1),(567,(0,1))),((1,2),(354,(0,0))),((1,3),(355,(0,0))),((1,4),(356,(0,0))),((2,0),(357,(0,0))),((2,1),(358,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_112_checked : successorFastRowCheck layer7 row6_112 row6_112choice = true := by decide
def row6_113 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2)]
def row6_113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(506,(1,0))),((-1,2),(645,(1,0))),((-1,3),(726,(1,0))),((0,0),(23,(0,0))),((0,4),(354,(0,0))),((1,-1),(568,(0,1))),((1,3),(360,(0,0))),((2,0),(361,(0,0))),((2,1),(362,(0,0))),((2,2),(363,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_113_checked : successorFastRowCheck layer7 row6_113 row6_113choice = true := by decide
def row6_114 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3)]
def row6_114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(507,(1,0))),((-1,2),(646,(1,0))),((-1,3),(727,(1,0))),((0,0),(24,(0,0))),((0,4),(355,(0,0))),((1,-1),(569,(0,1))),((1,2),(360,(0,0))),((1,4),(364,(0,0))),((2,0),(365,(0,0))),((2,1),(366,(0,0))),((2,3),(367,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_114_checked : successorFastRowCheck layer7 row6_114 row6_114choice = true := by decide
def row6_115 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)]
def row6_115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(508,(1,0))),((-1,2),(647,(1,0))),((-1,3),(728,(1,0))),((0,0),(25,(0,0))),((0,4),(357,(0,0))),((1,-1),(571,(0,1))),((1,2),(361,(0,0))),((1,3),(365,(0,0))),((2,-1),(573,(0,1))),((2,1),(368,(0,0))),((3,0),(369,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_115_checked : successorFastRowCheck layer7 row6_115 row6_115choice = true := by decide
def row6_116 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1)]
def row6_116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(509,(1,0))),((-1,2),(648,(1,0))),((-1,3),(729,(1,0))),((0,0),(26,(0,0))),((0,4),(358,(0,0))),((1,-1),(572,(0,1))),((1,2),(362,(0,0))),((1,3),(366,(0,0))),((2,0),(368,(0,0))),((2,2),(370,(0,0))),((3,1),(371,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_116_checked : successorFastRowCheck layer7 row6_116 row6_116choice = true := by decide
def row6_117 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1)]
def row6_117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(510,(1,0))),((-1,2),(649,(1,0))),((-1,3),(730,(1,0))),((0,0),(41,(0,0))),((0,4),(359,(0,0))),((1,0),(368,(0,0))),((1,2),(372,(0,0))),((1,3),(373,(0,0))),((2,-1),(574,(0,1))),((2,2),(374,(0,0))),((3,0),(375,(0,0))),((3,1),(376,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_117_checked : successorFastRowCheck layer7 row6_117 row6_117choice = true := by decide
def row6_118 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3)]
def row6_118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(511,(1,0))),((-1,2),(650,(1,0))),((0,0),(57,(0,0))),((0,3),(360,(0,0))),((1,-1),(575,(0,1))),((1,4),(379,(0,0))),((2,0),(380,(0,0))),((2,1),(381,(0,0))),((2,2),(382,(0,0))),((2,3),(383,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_118_checked : successorFastRowCheck layer7 row6_118 row6_118choice = true := by decide
def row6_119 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0)]
def row6_119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(512,(1,0))),((-1,2),(651,(1,0))),((0,0),(58,(0,0))),((0,3),(361,(0,0))),((1,-1),(577,(0,1))),((1,3),(380,(0,0))),((2,-1),(588,(0,1))),((2,1),(384,(0,0))),((2,2),(385,(0,0))),((3,0),(386,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_119_checked : successorFastRowCheck layer7 row6_119 row6_119choice = true := by decide
def Closure6C014rows : List (List GridPoint) := [row6_112,row6_113,row6_114,row6_115,row6_116,row6_117,row6_118,row6_119]
theorem Closure6C014_closed : ∀ row ∈ Closure6C014rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C014rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_112choice,row6_112_checked⟩
  · subst row
    exact ⟨row6_113choice,row6_113_checked⟩
  · subst row
    exact ⟨row6_114choice,row6_114_checked⟩
  · subst row
    exact ⟨row6_115choice,row6_115_checked⟩
  · subst row
    exact ⟨row6_116choice,row6_116_checked⟩
  · subst row
    exact ⟨row6_117choice,row6_117_checked⟩
  · subst row
    exact ⟨row6_118choice,row6_118_checked⟩
  · subst row
    exact ⟨row6_119choice,row6_119_checked⟩
end Polyomino57
