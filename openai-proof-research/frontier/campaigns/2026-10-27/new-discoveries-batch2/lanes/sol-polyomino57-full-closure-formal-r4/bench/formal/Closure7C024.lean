import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_192 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1)]
def row7_192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(985,(1,0))),((-1,1),(1651,(1,0))),((0,-1),(352,(0,1))),((0,2),(292,(0,0))),((1,0),(451,(0,0))),((1,2),(569,(0,0))),((2,-1),(1396,(0,1))),((2,3),(621,(0,0))),((3,0),(624,(0,0))),((3,2),(627,(0,0))),((4,1),(628,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_192_checked : successorFastRowCheck layer8 row7_192 row7_192choice = true := by decide
def row7_193 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2)]
def row7_193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(986,(1,0))),((-1,1),(1652,(1,0))),((0,-1),(353,(0,1))),((0,2),(293,(0,0))),((1,0),(452,(0,0))),((1,2),(570,(0,0))),((2,-1),(1397,(0,1))),((2,3),(622,(0,0))),((3,0),(625,(0,0))),((3,1),(627,(0,0))),((3,3),(629,(0,0))),((4,2),(630,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_193_checked : successorFastRowCheck layer8 row7_193 row7_193choice = true := by decide
def row7_194 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1)]
def row7_194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(987,(1,0))),((-1,1),(1653,(1,0))),((0,-1),(355,(0,1))),((0,2),(294,(0,0))),((1,0),(453,(0,0))),((1,2),(571,(0,0))),((2,-1),(1401,(0,1))),((2,2),(624,(0,0))),((3,-1),(1407,(0,1))),((3,2),(631,(0,0))),((4,0),(632,(0,0))),((4,1),(633,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_194_checked : successorFastRowCheck layer8 row7_194 row7_194choice = true := by decide
def row7_195 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0)]
def row7_195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(988,(1,0))),((-1,1),(1654,(1,0))),((0,-1),(356,(0,1))),((0,2),(295,(0,0))),((1,0),(454,(0,0))),((1,2),(572,(0,0))),((2,-1),(1402,(0,1))),((2,2),(626,(0,0))),((3,-1),(1409,(0,1))),((3,1),(632,(0,0))),((4,-1),(1410,(0,1))),((4,1),(634,(0,0))),((5,0),(635,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_195_checked : successorFastRowCheck layer8 row7_195 row7_195choice = true := by decide
def row7_196 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2)]
def row7_196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(989,(1,0))),((-1,1),(1655,(1,0))),((0,-1),(357,(0,1))),((0,2),(296,(0,0))),((1,0),(455,(0,0))),((1,2),(573,(0,0))),((2,-1),(1403,(0,1))),((2,2),(627,(0,0))),((3,0),(631,(0,0))),((3,3),(636,(0,0))),((4,1),(637,(0,0))),((4,2),(638,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_196_checked : successorFastRowCheck layer8 row7_196 row7_196choice = true := by decide
def row7_197 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1)]
def row7_197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(990,(1,0))),((-1,1),(1656,(1,0))),((0,-1),(358,(0,1))),((0,2),(297,(0,0))),((1,0),(456,(0,0))),((1,2),(574,(0,0))),((2,-1),(1404,(0,1))),((2,2),(628,(0,0))),((3,0),(633,(0,0))),((3,2),(637,(0,0))),((4,0),(639,(0,0))),((4,2),(640,(0,0))),((5,1),(641,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_197_checked : successorFastRowCheck layer8 row7_197 row7_197choice = true := by decide
def row7_198 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4)]
def row7_198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(991,(1,0))),((-1,1),(1657,(1,0))),((0,-1),(359,(0,1))),((0,2),(298,(0,0))),((1,0),(462,(0,0))),((1,2),(575,(0,0))),((1,3),(614,(0,0))),((1,4),(618,(0,0))),((2,0),(619,(0,0))),((2,5),(642,(0,0))),((3,1),(643,(0,0))),((3,2),(644,(0,0))),((3,3),(645,(0,0))),((3,4),(646,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_198_checked : successorFastRowCheck layer8 row7_198 row7_198choice = true := by decide
def row7_199 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1)]
def row7_199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(992,(1,0))),((-1,1),(1658,(1,0))),((0,-1),(360,(0,1))),((0,2),(299,(0,0))),((1,0),(463,(0,0))),((1,2),(576,(0,0))),((1,3),(615,(0,0))),((2,0),(621,(0,0))),((2,4),(643,(0,0))),((3,0),(647,(0,0))),((3,2),(648,(0,0))),((3,3),(649,(0,0))),((4,1),(650,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_199_checked : successorFastRowCheck layer8 row7_199 row7_199choice = true := by decide
def Closure7C024rows : List (List GridPoint) := [row7_192,row7_193,row7_194,row7_195,row7_196,row7_197,row7_198,row7_199]
theorem Closure7C024_closed : ∀ row ∈ Closure7C024rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C024rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_192choice,row7_192_checked⟩
  · subst row
    exact ⟨row7_193choice,row7_193_checked⟩
  · subst row
    exact ⟨row7_194choice,row7_194_checked⟩
  · subst row
    exact ⟨row7_195choice,row7_195_checked⟩
  · subst row
    exact ⟨row7_196choice,row7_196_checked⟩
  · subst row
    exact ⟨row7_197choice,row7_197_checked⟩
  · subst row
    exact ⟨row7_198choice,row7_198_checked⟩
  · subst row
    exact ⟨row7_199choice,row7_199_checked⟩
end Polyomino57
