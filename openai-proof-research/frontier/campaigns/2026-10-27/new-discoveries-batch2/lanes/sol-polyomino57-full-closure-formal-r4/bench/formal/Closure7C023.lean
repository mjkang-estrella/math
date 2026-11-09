import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_184 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2)]
def row7_184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(977,(1,0))),((-1,1),(1643,(1,0))),((0,-1),(340,(0,1))),((0,2),(284,(0,0))),((1,0),(443,(0,0))),((1,3),(555,(0,0))),((2,1),(577,(0,0))),((2,4),(594,(0,0))),((3,1),(597,(0,0))),((3,3),(598,(0,0))),((4,2),(599,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_184_checked : successorFastRowCheck layer8 row7_184 row7_184choice = true := by decide
def row7_185 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3)]
def row7_185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(978,(1,0))),((-1,1),(1644,(1,0))),((0,-1),(341,(0,1))),((0,2),(285,(0,0))),((1,0),(444,(0,0))),((1,3),(556,(0,0))),((2,1),(578,(0,0))),((2,4),(595,(0,0))),((3,2),(598,(0,0))),((3,4),(600,(0,0))),((4,3),(601,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_185_checked : successorFastRowCheck layer8 row7_185 row7_185choice = true := by decide
def row7_186 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2)]
def row7_186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(979,(1,0))),((-1,1),(1645,(1,0))),((0,-1),(342,(0,1))),((0,2),(286,(0,0))),((1,0),(445,(0,0))),((1,3),(557,(0,0))),((2,1),(580,(0,0))),((2,3),(597,(0,0))),((3,0),(602,(0,0))),((3,3),(603,(0,0))),((4,1),(604,(0,0))),((4,2),(605,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_186_checked : successorFastRowCheck layer8 row7_186 row7_186choice = true := by decide
def row7_187 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3)]
def row7_187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(980,(1,0))),((-1,1),(1646,(1,0))),((0,-1),(343,(0,1))),((0,2),(287,(0,0))),((1,0),(446,(0,0))),((1,3),(558,(0,0))),((2,1),(582,(0,0))),((2,3),(598,(0,0))),((3,1),(603,(0,0))),((3,4),(606,(0,0))),((4,2),(607,(0,0))),((4,3),(608,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_187_checked : successorFastRowCheck layer8 row7_187 row7_187choice = true := by decide
def row7_188 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2)]
def row7_188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(981,(1,0))),((-1,1),(1647,(1,0))),((0,-1),(344,(0,1))),((0,2),(288,(0,0))),((1,0),(447,(0,0))),((1,3),(559,(0,0))),((2,1),(583,(0,0))),((2,3),(599,(0,0))),((3,1),(605,(0,0))),((3,3),(607,(0,0))),((4,1),(609,(0,0))),((4,3),(610,(0,0))),((5,2),(611,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_188_checked : successorFastRowCheck layer8 row7_188 row7_188choice = true := by decide
def row7_189 : List GridPoint := [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3)]
def row7_189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(982,(1,0))),((-1,1),(1648,(1,0))),((0,-1),(345,(0,1))),((0,2),(289,(0,0))),((0,3),(402,(0,0))),((1,0),(448,(0,0))),((1,2),(545,(0,0))),((1,4),(612,(0,0))),((2,0),(613,(0,0))),((2,4),(614,(0,0))),((3,1),(615,(0,0))),((3,2),(616,(0,0))),((3,3),(617,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_189_checked : successorFastRowCheck layer8 row7_189 row7_189choice = true := by decide
def row7_190 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3)]
def row7_190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(983,(1,0))),((-1,1),(1649,(1,0))),((0,-1),(350,(0,1))),((0,2),(290,(0,0))),((1,0),(449,(0,0))),((1,2),(567,(0,0))),((1,3),(613,(0,0))),((2,-1),(1393,(0,1))),((2,4),(619,(0,0))),((3,0),(620,(0,0))),((3,1),(621,(0,0))),((3,2),(622,(0,0))),((3,3),(623,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_190_checked : successorFastRowCheck layer8 row7_190 row7_190choice = true := by decide
def row7_191 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0)]
def row7_191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(984,(1,0))),((-1,1),(1650,(1,0))),((0,-1),(351,(0,1))),((0,2),(291,(0,0))),((1,0),(450,(0,0))),((1,2),(568,(0,0))),((2,-1),(1395,(0,1))),((2,3),(620,(0,0))),((3,-1),(1406,(0,1))),((3,1),(624,(0,0))),((3,2),(625,(0,0))),((4,0),(626,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_191_checked : successorFastRowCheck layer8 row7_191 row7_191choice = true := by decide
def Closure7C023rows : List (List GridPoint) := [row7_184,row7_185,row7_186,row7_187,row7_188,row7_189,row7_190,row7_191]
theorem Closure7C023_closed : ∀ row ∈ Closure7C023rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C023rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_184choice,row7_184_checked⟩
  · subst row
    exact ⟨row7_185choice,row7_185_checked⟩
  · subst row
    exact ⟨row7_186choice,row7_186_checked⟩
  · subst row
    exact ⟨row7_187choice,row7_187_checked⟩
  · subst row
    exact ⟨row7_188choice,row7_188_checked⟩
  · subst row
    exact ⟨row7_189choice,row7_189_checked⟩
  · subst row
    exact ⟨row7_190choice,row7_190_checked⟩
  · subst row
    exact ⟨row7_191choice,row7_191_checked⟩
end Polyomino57
