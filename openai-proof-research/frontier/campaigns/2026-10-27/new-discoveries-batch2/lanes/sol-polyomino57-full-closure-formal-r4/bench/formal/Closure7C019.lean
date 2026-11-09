import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_152 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1)]
def row7_152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(945,(1,0))),((-1,1),(1611,(1,0))),((0,-1),(303,(0,1))),((0,2),(252,(0,0))),((1,-1),(1306,(0,1))),((1,1),(453,(0,0))),((2,-1),(1353,(0,1))),((2,2),(491,(0,0))),((3,-1),(1369,(0,1))),((3,2),(498,(0,0))),((4,0),(499,(0,0))),((4,1),(500,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_152_checked : successorFastRowCheck layer8 row7_152 row7_152choice = true := by decide
def row7_153 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0)]
def row7_153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(946,(1,0))),((-1,1),(1612,(1,0))),((0,-1),(304,(0,1))),((0,2),(253,(0,0))),((1,-1),(1307,(0,1))),((1,1),(454,(0,0))),((2,-1),(1354,(0,1))),((2,2),(493,(0,0))),((3,-1),(1371,(0,1))),((3,1),(499,(0,0))),((4,-1),(1372,(0,1))),((4,1),(501,(0,0))),((5,0),(502,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_153_checked : successorFastRowCheck layer8 row7_153 row7_153choice = true := by decide
def row7_154 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2)]
def row7_154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(947,(1,0))),((-1,1),(1613,(1,0))),((0,-1),(305,(0,1))),((0,2),(254,(0,0))),((1,-1),(1308,(0,1))),((1,1),(455,(0,0))),((2,-1),(1355,(0,1))),((2,2),(494,(0,0))),((3,0),(498,(0,0))),((3,3),(503,(0,0))),((4,1),(504,(0,0))),((4,2),(505,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_154_checked : successorFastRowCheck layer8 row7_154 row7_154choice = true := by decide
def row7_155 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1)]
def row7_155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(948,(1,0))),((-1,1),(1614,(1,0))),((0,-1),(306,(0,1))),((0,2),(255,(0,0))),((1,-1),(1309,(0,1))),((1,1),(456,(0,0))),((2,-1),(1356,(0,1))),((2,2),(495,(0,0))),((3,0),(500,(0,0))),((3,2),(504,(0,0))),((4,0),(506,(0,0))),((4,2),(507,(0,0))),((5,1),(508,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_155_checked : successorFastRowCheck layer8 row7_155 row7_155choice = true := by decide
def row7_156 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2)]
def row7_156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(949,(1,0))),((-1,1),(1615,(1,0))),((0,-1),(310,(0,1))),((0,2),(256,(0,0))),((1,-1),(1313,(0,1))),((1,1),(457,(0,0))),((2,-1),(1362,(0,1))),((2,1),(498,(0,0))),((2,2),(509,(0,0))),((3,-1),(1373,(0,1))),((3,3),(510,(0,0))),((4,0),(511,(0,0))),((4,1),(512,(0,0))),((4,2),(513,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_156_checked : successorFastRowCheck layer8 row7_156 row7_156choice = true := by decide
def row7_157 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0)]
def row7_157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(950,(1,0))),((-1,1),(1616,(1,0))),((0,-1),(311,(0,1))),((0,2),(257,(0,0))),((1,-1),(1314,(0,1))),((1,1),(458,(0,0))),((2,-1),(1363,(0,1))),((2,1),(499,(0,0))),((3,-1),(1375,(0,1))),((3,2),(511,(0,0))),((4,-1),(1381,(0,1))),((4,1),(514,(0,0))),((5,0),(515,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_157_checked : successorFastRowCheck layer8 row7_157 row7_157choice = true := by decide
def row7_158 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1)]
def row7_158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(951,(1,0))),((-1,1),(1617,(1,0))),((0,-1),(312,(0,1))),((0,2),(258,(0,0))),((1,-1),(1315,(0,1))),((1,1),(459,(0,0))),((2,-1),(1364,(0,1))),((2,1),(500,(0,0))),((3,-1),(1376,(0,1))),((3,2),(512,(0,0))),((4,0),(514,(0,0))),((4,2),(516,(0,0))),((5,1),(517,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_158_checked : successorFastRowCheck layer8 row7_158 row7_158choice = true := by decide
def row7_159 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1)]
def row7_159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(952,(1,0))),((-1,1),(1618,(1,0))),((0,-1),(314,(0,1))),((0,2),(259,(0,0))),((1,-1),(1317,(0,1))),((1,1),(460,(0,0))),((2,-1),(1366,(0,1))),((2,1),(501,(0,0))),((3,-1),(1379,(0,1))),((3,1),(514,(0,0))),((4,-1),(1382,(0,1))),((4,2),(518,(0,0))),((5,0),(519,(0,0))),((5,1),(520,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_159_checked : successorFastRowCheck layer8 row7_159 row7_159choice = true := by decide
def Closure7C019rows : List (List GridPoint) := [row7_152,row7_153,row7_154,row7_155,row7_156,row7_157,row7_158,row7_159]
theorem Closure7C019_closed : ∀ row ∈ Closure7C019rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C019rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_152choice,row7_152_checked⟩
  · subst row
    exact ⟨row7_153choice,row7_153_checked⟩
  · subst row
    exact ⟨row7_154choice,row7_154_checked⟩
  · subst row
    exact ⟨row7_155choice,row7_155_checked⟩
  · subst row
    exact ⟨row7_156choice,row7_156_checked⟩
  · subst row
    exact ⟨row7_157choice,row7_157_checked⟩
  · subst row
    exact ⟨row7_158choice,row7_158_checked⟩
  · subst row
    exact ⟨row7_159choice,row7_159_checked⟩
end Polyomino57
