import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_128 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0)]
def row6_128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(521,(1,0))),((-1,2),(660,(1,0))),((0,0),(90,(0,0))),((0,3),(375,(0,0))),((1,0),(392,(0,0))),((1,2),(405,(0,0))),((2,-1),(596,(0,1))),((2,2),(409,(0,0))),((3,-1),(598,(0,1))),((3,1),(412,(0,0))),((4,0),(413,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_128_checked : successorFastRowCheck layer7 row6_128 row6_128choice = true := by decide
def row6_129 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1)]
def row6_129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(522,(1,0))),((-1,2),(661,(1,0))),((0,0),(91,(0,0))),((0,3),(376,(0,0))),((1,0),(393,(0,0))),((1,2),(406,(0,0))),((2,-1),(597,(0,1))),((2,2),(410,(0,0))),((3,0),(412,(0,0))),((3,2),(414,(0,0))),((4,1),(415,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_129_checked : successorFastRowCheck layer7 row6_129 row6_129choice = true := by decide
def row6_130 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1)]
def row6_130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(523,(1,0))),((-1,2),(662,(1,0))),((0,0),(95,(0,0))),((0,3),(377,(0,0))),((1,0),(399,(0,0))),((1,2),(407,(0,0))),((2,0),(412,(0,0))),((2,2),(416,(0,0))),((3,-1),(599,(0,1))),((3,2),(417,(0,0))),((4,0),(418,(0,0))),((4,1),(419,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_130_checked : successorFastRowCheck layer7 row6_130 row6_130choice = true := by decide
def row6_131 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2)]
def row6_131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(524,(1,0))),((-1,2),(663,(1,0))),((0,0),(107,(0,0))),((0,3),(378,(0,0))),((1,0),(402,(0,0))),((1,1),(404,(0,0))),((1,3),(421,(0,0))),((2,-1),(600,(0,1))),((2,3),(422,(0,0))),((3,0),(423,(0,0))),((3,1),(424,(0,0))),((3,2),(425,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_131_checked : successorFastRowCheck layer7 row6_131 row6_131choice = true := by decide
def row6_132 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row6_132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(525,(1,0))),((-1,3),(731,(1,0))),((0,0),(118,(0,0))),((0,2),(360,(0,0))),((0,4),(428,(0,0))),((1,-1),(601,(0,1))),((1,4),(429,(0,0))),((2,0),(430,(0,0))),((2,1),(431,(0,0))),((2,2),(432,(0,0))),((2,3),(433,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_132_checked : successorFastRowCheck layer7 row6_132 row6_132choice = true := by decide
def row6_133 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row6_133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(526,(1,0))),((0,0),(124,(0,0))),((0,2),(379,(0,0))),((0,3),(429,(0,0))),((0,4),(435,(0,0))),((1,-1),(602,(0,1))),((1,5),(436,(0,0))),((2,0),(437,(0,0))),((2,1),(438,(0,0))),((2,2),(439,(0,0))),((2,3),(440,(0,0))),((2,4),(441,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_133_checked : successorFastRowCheck layer7 row6_133 row6_133choice = true := by decide
def row6_134 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row6_134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(527,(1,0))),((0,0),(125,(0,0))),((0,2),(380,(0,0))),((0,3),(430,(0,0))),((1,-1),(604,(0,1))),((1,4),(437,(0,0))),((2,-1),(644,(0,1))),((2,1),(442,(0,0))),((2,2),(443,(0,0))),((2,3),(444,(0,0))),((3,0),(445,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_134_checked : successorFastRowCheck layer7 row6_134 row6_134choice = true := by decide
def row6_135 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row6_135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(528,(1,0))),((0,0),(126,(0,0))),((0,2),(381,(0,0))),((0,3),(431,(0,0))),((1,-1),(605,(0,1))),((1,4),(438,(0,0))),((2,0),(442,(0,0))),((2,2),(446,(0,0))),((2,3),(447,(0,0))),((3,1),(448,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_135_checked : successorFastRowCheck layer7 row6_135 row6_135choice = true := by decide
def Closure6C016rows : List (List GridPoint) := [row6_128,row6_129,row6_130,row6_131,row6_132,row6_133,row6_134,row6_135]
theorem Closure6C016_closed : ∀ row ∈ Closure6C016rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C016rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_128choice,row6_128_checked⟩
  · subst row
    exact ⟨row6_129choice,row6_129_checked⟩
  · subst row
    exact ⟨row6_130choice,row6_130_checked⟩
  · subst row
    exact ⟨row6_131choice,row6_131_checked⟩
  · subst row
    exact ⟨row6_132choice,row6_132_checked⟩
  · subst row
    exact ⟨row6_133choice,row6_133_checked⟩
  · subst row
    exact ⟨row6_134choice,row6_134_checked⟩
  · subst row
    exact ⟨row6_135choice,row6_135_checked⟩
end Polyomino57
