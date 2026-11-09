import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_152 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2)]
def row6_152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(545,(1,0))),((0,0),(143,(0,0))),((0,2),(398,(0,0))),((1,-1),(635,(0,1))),((1,2),(463,(0,0))),((2,0),(477,(0,0))),((2,3),(489,(0,0))),((3,1),(492,(0,0))),((3,3),(494,(0,0))),((4,2),(495,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_152_checked : successorFastRowCheck layer7 row6_152 row6_152choice = true := by decide
def row6_153 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1)]
def row6_153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(546,(1,0))),((0,0),(144,(0,0))),((0,2),(399,(0,0))),((1,-1),(636,(0,1))),((1,2),(464,(0,0))),((2,0),(478,(0,0))),((2,2),(491,(0,0))),((3,-1),(663,(0,1))),((3,2),(496,(0,0))),((4,0),(497,(0,0))),((4,1),(498,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_153_checked : successorFastRowCheck layer7 row6_153 row6_153choice = true := by decide
def row6_154 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2)]
def row6_154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(547,(1,0))),((0,0),(145,(0,0))),((0,2),(400,(0,0))),((1,-1),(637,(0,1))),((1,2),(465,(0,0))),((2,0),(480,(0,0))),((2,2),(492,(0,0))),((3,0),(496,(0,0))),((3,3),(499,(0,0))),((4,1),(500,(0,0))),((4,2),(501,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_154_checked : successorFastRowCheck layer7 row6_154 row6_154choice = true := by decide
def row6_155 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1)]
def row6_155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(548,(1,0))),((0,0),(146,(0,0))),((0,2),(401,(0,0))),((1,-1),(638,(0,1))),((1,2),(466,(0,0))),((2,0),(481,(0,0))),((2,2),(493,(0,0))),((3,0),(498,(0,0))),((3,2),(500,(0,0))),((4,0),(502,(0,0))),((4,2),(503,(0,0))),((5,1),(504,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_155_checked : successorFastRowCheck layer7 row6_155 row6_155choice = true := by decide
def row6_156 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row6_156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(549,(1,0))),((0,0),(166,(0,0))),((0,2),(403,(0,0))),((0,3),(434,(0,0))),((1,0),(442,(0,0))),((1,4),(505,(0,0))),((2,-1),(664,(0,1))),((2,2),(506,(0,0))),((2,3),(507,(0,0))),((3,0),(508,(0,0))),((3,1),(509,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_156_checked : successorFastRowCheck layer7 row6_156 row6_156choice = true := by decide
def row6_157 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row6_157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(550,(1,0))),((0,0),(174,(0,0))),((0,2),(404,(0,0))),((1,0),(453,(0,0))),((1,3),(506,(0,0))),((2,-1),(665,(0,1))),((2,3),(511,(0,0))),((3,0),(512,(0,0))),((3,1),(513,(0,0))),((3,2),(514,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_157_checked : successorFastRowCheck layer7 row6_157 row6_157choice = true := by decide
def row6_158 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row6_158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(551,(1,0))),((0,0),(175,(0,0))),((0,2),(405,(0,0))),((1,0),(454,(0,0))),((1,3),(508,(0,0))),((2,-1),(667,(0,1))),((2,2),(512,(0,0))),((3,-1),(669,(0,1))),((3,1),(515,(0,0))),((4,0),(516,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_158_checked : successorFastRowCheck layer7 row6_158 row6_158choice = true := by decide
def row6_159 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row6_159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(552,(1,0))),((0,0),(176,(0,0))),((0,2),(406,(0,0))),((1,0),(455,(0,0))),((1,3),(509,(0,0))),((2,-1),(668,(0,1))),((2,2),(513,(0,0))),((3,0),(515,(0,0))),((3,2),(517,(0,0))),((4,1),(518,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_159_checked : successorFastRowCheck layer7 row6_159 row6_159choice = true := by decide
def Closure6C019rows : List (List GridPoint) := [row6_152,row6_153,row6_154,row6_155,row6_156,row6_157,row6_158,row6_159]
theorem Closure6C019_closed : ∀ row ∈ Closure6C019rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C019rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_152choice,row6_152_checked⟩
  · subst row
    exact ⟨row6_153choice,row6_153_checked⟩
  · subst row
    exact ⟨row6_154choice,row6_154_checked⟩
  · subst row
    exact ⟨row6_155choice,row6_155_checked⟩
  · subst row
    exact ⟨row6_156choice,row6_156_checked⟩
  · subst row
    exact ⟨row6_157choice,row6_157_checked⟩
  · subst row
    exact ⟨row6_158choice,row6_158_checked⟩
  · subst row
    exact ⟨row6_159choice,row6_159_checked⟩
end Polyomino57
