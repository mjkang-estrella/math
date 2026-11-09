import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_192 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row6_192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(682,(1,0))),((0,0),(232,(0,0))),((0,1),(390,(0,0))),((0,3),(586,(0,0))),((1,-1),(721,(0,1))),((1,3),(616,(0,0))),((2,0),(624,(0,0))),((2,1),(629,(0,0))),((2,3),(634,(0,0))),((3,1),(636,(0,0))),((3,3),(637,(0,0))),((4,2),(638,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_192_checked : successorFastRowCheck layer7 row6_192 row6_192choice = true := by decide
def row6_193 : List GridPoint := [(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row6_193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(683,(1,0))),((0,0),(233,(0,0))),((0,1),(402,(0,0))),((0,3),(587,(0,0))),((1,-1),(722,(0,1))),((1,1),(619,(0,0))),((1,3),(639,(0,0))),((2,-1),(731,(0,1))),((2,3),(640,(0,0))),((3,0),(641,(0,0))),((3,1),(642,(0,0))),((3,2),(643,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_193_checked : successorFastRowCheck layer7 row6_193 row6_193choice = true := by decide
def row6_194 : List GridPoint := [(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row6_194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(684,(1,0))),((0,1),(403,(0,0))),((0,3),(588,(0,0))),((1,0),(608,(0,0))),((1,4),(644,(0,0))),((2,-1),(732,(0,1))),((2,2),(645,(0,0))),((2,3),(646,(0,0))),((3,0),(647,(0,0))),((3,1),(648,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_194_checked : successorFastRowCheck layer7 row6_194 row6_194choice = true := by decide
def row6_195 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row6_195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(685,(1,0))),((0,1),(404,(0,0))),((0,3),(589,(0,0))),((1,0),(619,(0,0))),((1,3),(645,(0,0))),((2,-1),(733,(0,1))),((2,3),(650,(0,0))),((3,0),(651,(0,0))),((3,1),(652,(0,0))),((3,2),(653,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_195_checked : successorFastRowCheck layer7 row6_195 row6_195choice = true := by decide
def row6_196 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row6_196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(686,(1,0))),((0,1),(405,(0,0))),((0,3),(590,(0,0))),((1,0),(620,(0,0))),((1,3),(647,(0,0))),((2,-1),(735,(0,1))),((2,2),(651,(0,0))),((3,-1),(737,(0,1))),((3,1),(654,(0,0))),((4,0),(655,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_196_checked : successorFastRowCheck layer7 row6_196 row6_196choice = true := by decide
def row6_197 : List GridPoint := [(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row6_197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(687,(1,0))),((0,1),(406,(0,0))),((0,3),(591,(0,0))),((1,0),(621,(0,0))),((1,3),(648,(0,0))),((2,-1),(736,(0,1))),((2,2),(652,(0,0))),((3,0),(654,(0,0))),((3,2),(656,(0,0))),((4,1),(657,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_197_checked : successorFastRowCheck layer7 row6_197 row6_197choice = true := by decide
def row6_198 : List GridPoint := [(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row6_198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(688,(1,0))),((0,1),(407,(0,0))),((0,3),(592,(0,0))),((1,0),(630,(0,0))),((1,3),(649,(0,0))),((2,0),(654,(0,0))),((2,2),(658,(0,0))),((3,-1),(738,(0,1))),((3,2),(659,(0,0))),((4,0),(660,(0,0))),((4,1),(661,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_198_checked : successorFastRowCheck layer7 row6_198 row6_198choice = true := by decide
def row6_199 : List GridPoint := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)]
def row6_199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(689,(1,0))),((0,1),(421,(0,0))),((0,3),(593,(0,0))),((1,0),(639,(0,0))),((1,1),(645,(0,0))),((1,4),(664,(0,0))),((2,-1),(739,(0,1))),((2,3),(665,(0,0))),((3,0),(666,(0,0))),((3,1),(667,(0,0))),((3,2),(668,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_199_checked : successorFastRowCheck layer7 row6_199 row6_199choice = true := by decide
def Closure6C024rows : List (List GridPoint) := [row6_192,row6_193,row6_194,row6_195,row6_196,row6_197,row6_198,row6_199]
theorem Closure6C024_closed : ∀ row ∈ Closure6C024rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C024rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_192choice,row6_192_checked⟩
  · subst row
    exact ⟨row6_193choice,row6_193_checked⟩
  · subst row
    exact ⟨row6_194choice,row6_194_checked⟩
  · subst row
    exact ⟨row6_195choice,row6_195_checked⟩
  · subst row
    exact ⟨row6_196choice,row6_196_checked⟩
  · subst row
    exact ⟨row6_197choice,row6_197_checked⟩
  · subst row
    exact ⟨row6_198choice,row6_198_checked⟩
  · subst row
    exact ⟨row6_199choice,row6_199_checked⟩
end Polyomino57
