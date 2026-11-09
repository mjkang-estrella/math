import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_120 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1)]
def row6_120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(513,(1,0))),((-1,2),(652,(1,0))),((0,0),(59,(0,0))),((0,3),(362,(0,0))),((1,-1),(578,(0,1))),((1,3),(381,(0,0))),((2,0),(384,(0,0))),((2,2),(387,(0,0))),((3,1),(388,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_120_checked : successorFastRowCheck layer7 row6_120 row6_120choice = true := by decide
def row6_121 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2)]
def row6_121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(514,(1,0))),((-1,2),(653,(1,0))),((0,0),(60,(0,0))),((0,3),(363,(0,0))),((1,-1),(579,(0,1))),((1,3),(382,(0,0))),((2,0),(385,(0,0))),((2,1),(387,(0,0))),((2,3),(389,(0,0))),((3,2),(390,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_121_checked : successorFastRowCheck layer7 row6_121 row6_121choice = true := by decide
def row6_122 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1)]
def row6_122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(515,(1,0))),((-1,2),(654,(1,0))),((0,0),(61,(0,0))),((0,3),(368,(0,0))),((1,-1),(583,(0,1))),((1,2),(384,(0,0))),((2,-1),(589,(0,1))),((2,2),(391,(0,0))),((3,0),(392,(0,0))),((3,1),(393,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_122_checked : successorFastRowCheck layer7 row6_122 row6_122choice = true := by decide
def row6_123 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0)]
def row6_123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(516,(1,0))),((-1,2),(655,(1,0))),((0,0),(62,(0,0))),((0,3),(369,(0,0))),((1,-1),(584,(0,1))),((1,2),(386,(0,0))),((2,-1),(591,(0,1))),((2,1),(392,(0,0))),((3,-1),(592,(0,1))),((3,1),(394,(0,0))),((4,0),(395,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_123_checked : successorFastRowCheck layer7 row6_123 row6_123choice = true := by decide
def row6_124 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2)]
def row6_124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(517,(1,0))),((-1,2),(656,(1,0))),((0,0),(63,(0,0))),((0,3),(370,(0,0))),((1,-1),(585,(0,1))),((1,2),(387,(0,0))),((2,0),(391,(0,0))),((2,3),(396,(0,0))),((3,1),(397,(0,0))),((3,2),(398,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_124_checked : successorFastRowCheck layer7 row6_124 row6_124choice = true := by decide
def row6_125 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1)]
def row6_125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(518,(1,0))),((-1,2),(657,(1,0))),((0,0),(64,(0,0))),((0,3),(371,(0,0))),((1,-1),(586,(0,1))),((1,2),(388,(0,0))),((2,0),(393,(0,0))),((2,2),(397,(0,0))),((3,0),(399,(0,0))),((3,2),(400,(0,0))),((4,1),(401,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_125_checked : successorFastRowCheck layer7 row6_125 row6_125choice = true := by decide
def row6_126 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1)]
def row6_126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(519,(1,0))),((-1,2),(658,(1,0))),((0,0),(84,(0,0))),((0,3),(372,(0,0))),((1,0),(384,(0,0))),((1,3),(403,(0,0))),((2,-1),(593,(0,1))),((2,2),(404,(0,0))),((3,0),(405,(0,0))),((3,1),(406,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_126_checked : successorFastRowCheck layer7 row6_126 row6_126choice = true := by decide
def row6_127 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2)]
def row6_127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(520,(1,0))),((-1,2),(659,(1,0))),((0,0),(89,(0,0))),((0,3),(374,(0,0))),((1,0),(391,(0,0))),((1,2),(404,(0,0))),((2,-1),(594,(0,1))),((2,3),(408,(0,0))),((3,0),(409,(0,0))),((3,1),(410,(0,0))),((3,2),(411,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_127_checked : successorFastRowCheck layer7 row6_127 row6_127choice = true := by decide
def Closure6C015rows : List (List GridPoint) := [row6_120,row6_121,row6_122,row6_123,row6_124,row6_125,row6_126,row6_127]
theorem Closure6C015_closed : ∀ row ∈ Closure6C015rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C015rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_120choice,row6_120_checked⟩
  · subst row
    exact ⟨row6_121choice,row6_121_checked⟩
  · subst row
    exact ⟨row6_122choice,row6_122_checked⟩
  · subst row
    exact ⟨row6_123choice,row6_123_checked⟩
  · subst row
    exact ⟨row6_124choice,row6_124_checked⟩
  · subst row
    exact ⟨row6_125choice,row6_125_checked⟩
  · subst row
    exact ⟨row6_126choice,row6_126_checked⟩
  · subst row
    exact ⟨row6_127choice,row6_127_checked⟩
end Polyomino57
