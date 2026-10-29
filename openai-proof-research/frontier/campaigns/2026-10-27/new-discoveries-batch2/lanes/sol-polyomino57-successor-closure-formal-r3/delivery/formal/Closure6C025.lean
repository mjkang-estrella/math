import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_200 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)]
def row6_200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(690,(1,0))),((0,1),(422,(0,0))),((0,3),(594,(0,0))),((1,0),(640,(0,0))),((1,1),(650,(0,0))),((1,3),(665,(0,0))),((2,-1),(740,(0,1))),((2,4),(671,(0,0))),((3,0),(672,(0,0))),((3,1),(673,(0,0))),((3,2),(674,(0,0))),((3,3),(675,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_200_checked : successorFastRowCheck layer7 row6_200 row6_200choice = true := by decide
def row6_201 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)]
def row6_201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(691,(1,0))),((0,1),(423,(0,0))),((0,3),(595,(0,0))),((1,0),(641,(0,0))),((1,1),(651,(0,0))),((1,3),(666,(0,0))),((2,-1),(742,(0,1))),((2,3),(672,(0,0))),((3,-1),(745,(0,1))),((3,1),(676,(0,0))),((3,2),(677,(0,0))),((4,0),(678,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_201_checked : successorFastRowCheck layer7 row6_201 row6_201choice = true := by decide
def row6_202 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)]
def row6_202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(692,(1,0))),((0,1),(424,(0,0))),((0,3),(596,(0,0))),((1,0),(642,(0,0))),((1,1),(652,(0,0))),((1,3),(667,(0,0))),((2,-1),(743,(0,1))),((2,3),(673,(0,0))),((3,0),(676,(0,0))),((3,2),(679,(0,0))),((4,1),(680,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_202_checked : successorFastRowCheck layer7 row6_202 row6_202choice = true := by decide
def row6_203 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)]
def row6_203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(693,(1,0))),((0,1),(425,(0,0))),((0,3),(597,(0,0))),((1,0),(643,(0,0))),((1,1),(653,(0,0))),((1,3),(668,(0,0))),((2,-1),(744,(0,1))),((2,3),(674,(0,0))),((3,0),(677,(0,0))),((3,1),(679,(0,0))),((3,3),(681,(0,0))),((4,2),(682,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_203_checked : successorFastRowCheck layer7 row6_203 row6_203choice = true := by decide
def row6_204 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)]
def row6_204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(694,(1,0))),((0,1),(426,(0,0))),((0,3),(598,(0,0))),((1,1),(658,(0,0))),((1,3),(669,(0,0))),((2,0),(676,(0,0))),((2,3),(684,(0,0))),((3,-1),(746,(0,1))),((3,2),(685,(0,0))),((4,0),(686,(0,0))),((4,1),(687,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_204_checked : successorFastRowCheck layer7 row6_204 row6_204choice = true := by decide
def row6_205 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)]
def row6_205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(695,(1,0))),((0,1),(427,(0,0))),((0,3),(599,(0,0))),((1,1),(663,(0,0))),((1,3),(670,(0,0))),((2,0),(683,(0,0))),((2,1),(685,(0,0))),((2,3),(689,(0,0))),((3,-1),(747,(0,1))),((3,3),(690,(0,0))),((4,0),(691,(0,0))),((4,1),(692,(0,0))),((4,2),(693,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_205_checked : successorFastRowCheck layer7 row6_205 row6_205choice = true := by decide
def row6_206 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def row6_206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(739,(1,0))),((-1,4),(757,(1,0))),((0,0),(234,(0,0))),((0,1),(428,(0,0))),((0,2),(568,(0,0))),((0,5),(696,(0,0))),((1,-1),(748,(0,1))),((1,4),(697,(0,0))),((2,0),(698,(0,0))),((2,1),(699,(0,0))),((2,2),(700,(0,0))),((2,3),(701,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_206_checked : successorFastRowCheck layer7 row6_206 row6_206choice = true := by decide
def row6_207 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row6_207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(740,(1,0))),((0,0),(235,(0,0))),((0,1),(429,(0,0))),((0,2),(575,(0,0))),((0,4),(697,(0,0))),((1,-1),(749,(0,1))),((1,5),(705,(0,0))),((2,0),(706,(0,0))),((2,1),(707,(0,0))),((2,2),(708,(0,0))),((2,3),(709,(0,0))),((2,4),(710,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_207_checked : successorFastRowCheck layer7 row6_207 row6_207choice = true := by decide
def Closure6C025rows : List (List GridPoint) := [row6_200,row6_201,row6_202,row6_203,row6_204,row6_205,row6_206,row6_207]
theorem Closure6C025_closed : ∀ row ∈ Closure6C025rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C025rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_200choice,row6_200_checked⟩
  · subst row
    exact ⟨row6_201choice,row6_201_checked⟩
  · subst row
    exact ⟨row6_202choice,row6_202_checked⟩
  · subst row
    exact ⟨row6_203choice,row6_203_checked⟩
  · subst row
    exact ⟨row6_204choice,row6_204_checked⟩
  · subst row
    exact ⟨row6_205choice,row6_205_checked⟩
  · subst row
    exact ⟨row6_206choice,row6_206_checked⟩
  · subst row
    exact ⟨row6_207choice,row6_207_checked⟩
end Polyomino57
