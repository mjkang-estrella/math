import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_256 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def row7_256choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1049,(1,0))),((0,-1),(539,(0,1))),((0,1),(426,(0,0))),((0,2),(732,(0,0))),((0,3),(780,(0,0))),((1,-1),(1480,(0,1))),((1,4),(812,(0,0))),((2,0),(823,(0,0))),((2,1),(831,(0,0))),((2,2),(837,(0,0))),((2,5),(843,(0,0))),((3,3),(844,(0,0))),((3,4),(845,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_256_checked : successorFastRowCheck layer8 row7_256 row7_256choice = true := by decide
def row7_257 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def row7_257choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1050,(1,0))),((0,-1),(540,(0,1))),((0,1),(427,(0,0))),((0,2),(733,(0,0))),((0,3),(781,(0,0))),((1,-1),(1481,(0,1))),((1,4),(813,(0,0))),((2,0),(825,(0,0))),((2,1),(833,(0,0))),((2,2),(839,(0,0))),((2,4),(844,(0,0))),((3,2),(846,(0,0))),((3,4),(847,(0,0))),((4,3),(848,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_257_checked : successorFastRowCheck layer8 row7_257 row7_257choice = true := by decide
def row7_258 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def row7_258choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1051,(1,0))),((0,-1),(545,(0,1))),((0,1),(428,(0,0))),((0,2),(734,(0,0))),((1,-1),(1494,(0,1))),((1,3),(816,(0,0))),((2,-1),(1682,(0,1))),((2,3),(850,(0,0))),((3,0),(851,(0,0))),((3,1),(852,(0,0))),((3,2),(853,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_258_checked : successorFastRowCheck layer8 row7_258 row7_258choice = true := by decide
def row7_259 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def row7_259choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1052,(1,0))),((0,-1),(546,(0,1))),((0,1),(429,(0,0))),((0,2),(735,(0,0))),((1,-1),(1495,(0,1))),((1,3),(818,(0,0))),((2,-1),(1684,(0,1))),((2,2),(851,(0,0))),((3,-1),(1694,(0,1))),((3,1),(854,(0,0))),((4,0),(855,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_259_checked : successorFastRowCheck layer8 row7_259 row7_259choice = true := by decide
def row7_260 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_260choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1053,(1,0))),((0,-1),(547,(0,1))),((0,1),(430,(0,0))),((0,2),(736,(0,0))),((1,-1),(1496,(0,1))),((1,3),(819,(0,0))),((2,-1),(1685,(0,1))),((2,2),(852,(0,0))),((3,0),(854,(0,0))),((3,2),(856,(0,0))),((4,1),(857,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_260_checked : successorFastRowCheck layer8 row7_260 row7_260choice = true := by decide
def row7_261 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def row7_261choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1054,(1,0))),((0,-1),(548,(0,1))),((0,1),(431,(0,0))),((0,2),(737,(0,0))),((1,-1),(1497,(0,1))),((1,3),(820,(0,0))),((2,-1),(1686,(0,1))),((2,1),(850,(0,0))),((2,4),(858,(0,0))),((3,0),(859,(0,0))),((3,2),(860,(0,0))),((3,3),(861,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_261_checked : successorFastRowCheck layer8 row7_261 row7_261choice = true := by decide
def row7_262 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def row7_262choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1055,(1,0))),((0,-1),(549,(0,1))),((0,1),(432,(0,0))),((0,2),(738,(0,0))),((1,-1),(1498,(0,1))),((1,3),(821,(0,0))),((2,-1),(1688,(0,1))),((2,1),(851,(0,0))),((2,3),(859,(0,0))),((3,-1),(1695,(0,1))),((3,1),(862,(0,0))),((3,2),(863,(0,0))),((4,0),(864,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_262_checked : successorFastRowCheck layer8 row7_262 row7_262choice = true := by decide
def row7_263 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def row7_263choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1056,(1,0))),((0,-1),(550,(0,1))),((0,1),(433,(0,0))),((0,2),(739,(0,0))),((1,-1),(1499,(0,1))),((1,3),(822,(0,0))),((2,-1),(1689,(0,1))),((2,1),(853,(0,0))),((2,3),(860,(0,0))),((3,0),(863,(0,0))),((3,1),(865,(0,0))),((3,3),(866,(0,0))),((4,2),(867,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_263_checked : successorFastRowCheck layer8 row7_263 row7_263choice = true := by decide
def Closure7C032rows : List (List GridPoint) := [row7_256,row7_257,row7_258,row7_259,row7_260,row7_261,row7_262,row7_263]
theorem Closure7C032_closed : ∀ row ∈ Closure7C032rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C032rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_256choice,row7_256_checked⟩
  · subst row
    exact ⟨row7_257choice,row7_257_checked⟩
  · subst row
    exact ⟨row7_258choice,row7_258_checked⟩
  · subst row
    exact ⟨row7_259choice,row7_259_checked⟩
  · subst row
    exact ⟨row7_260choice,row7_260_checked⟩
  · subst row
    exact ⟨row7_261choice,row7_261_checked⟩
  · subst row
    exact ⟨row7_262choice,row7_262_checked⟩
  · subst row
    exact ⟨row7_263choice,row7_263_checked⟩
end Polyomino57
