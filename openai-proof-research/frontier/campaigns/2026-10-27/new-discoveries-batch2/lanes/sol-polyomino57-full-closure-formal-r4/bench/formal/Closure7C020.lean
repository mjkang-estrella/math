import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_160 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0)]
def row7_160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(953,(1,0))),((-1,1),(1619,(1,0))),((0,-1),(315,(0,1))),((0,2),(260,(0,0))),((1,-1),(1318,(0,1))),((1,1),(461,(0,0))),((2,-1),(1367,(0,1))),((2,1),(502,(0,0))),((3,-1),(1380,(0,1))),((3,1),(515,(0,0))),((4,-1),(1384,(0,1))),((4,1),(519,(0,0))),((5,-1),(1385,(0,1))),((5,1),(521,(0,0))),((6,0),(522,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_160_checked : successorFastRowCheck layer8 row7_160 row7_160choice = true := by decide
def row7_161 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(954,(1,0))),((-1,1),(1620,(1,0))),((0,-1),(316,(0,1))),((0,2),(261,(0,0))),((0,3),(389,(0,0))),((0,4),(405,(0,0))),((0,5),(410,(0,0))),((1,0),(411,(0,0))),((1,6),(523,(0,0))),((2,1),(524,(0,0))),((2,2),(525,(0,0))),((2,3),(526,(0,0))),((2,4),(527,(0,0))),((2,5),(528,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_161_checked : successorFastRowCheck layer8 row7_161 row7_161choice = true := by decide
def row7_162 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(955,(1,0))),((-1,1),(1621,(1,0))),((0,-1),(317,(0,1))),((0,2),(262,(0,0))),((0,3),(390,(0,0))),((0,4),(406,(0,0))),((1,0),(413,(0,0))),((1,5),(524,(0,0))),((2,0),(529,(0,0))),((2,2),(530,(0,0))),((2,3),(531,(0,0))),((2,4),(532,(0,0))),((3,1),(533,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_162_checked : successorFastRowCheck layer8 row7_162 row7_162choice = true := by decide
def row7_163 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(956,(1,0))),((-1,1),(1622,(1,0))),((0,-1),(318,(0,1))),((0,2),(263,(0,0))),((0,3),(391,(0,0))),((0,4),(407,(0,0))),((1,0),(414,(0,0))),((1,5),(525,(0,0))),((2,1),(530,(0,0))),((2,3),(534,(0,0))),((2,4),(535,(0,0))),((3,2),(536,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_163_checked : successorFastRowCheck layer8 row7_163 row7_163choice = true := by decide
def row7_164 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(957,(1,0))),((-1,1),(1623,(1,0))),((0,-1),(319,(0,1))),((0,2),(264,(0,0))),((0,3),(392,(0,0))),((0,4),(408,(0,0))),((1,0),(415,(0,0))),((1,5),(526,(0,0))),((2,1),(531,(0,0))),((2,2),(534,(0,0))),((2,4),(537,(0,0))),((3,3),(538,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_164_checked : successorFastRowCheck layer8 row7_164 row7_164choice = true := by decide
def row7_165 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(958,(1,0))),((-1,1),(1624,(1,0))),((0,-1),(320,(0,1))),((0,2),(265,(0,0))),((0,3),(393,(0,0))),((0,4),(409,(0,0))),((1,0),(416,(0,0))),((1,5),(527,(0,0))),((2,1),(532,(0,0))),((2,2),(535,(0,0))),((2,3),(537,(0,0))),((2,5),(539,(0,0))),((3,4),(540,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_165_checked : successorFastRowCheck layer8 row7_165 row7_165choice = true := by decide
def row7_166 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(959,(1,0))),((-1,1),(1625,(1,0))),((0,-1),(321,(0,1))),((0,2),(266,(0,0))),((0,3),(394,(0,0))),((1,0),(417,(0,0))),((1,4),(529,(0,0))),((2,-1),(1386,(0,1))),((2,2),(541,(0,0))),((2,3),(542,(0,0))),((3,0),(543,(0,0))),((3,1),(544,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_166_checked : successorFastRowCheck layer8 row7_166 row7_166choice = true := by decide
def row7_167 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2)]
def row7_167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(960,(1,0))),((-1,1),(1626,(1,0))),((0,-1),(322,(0,1))),((0,2),(267,(0,0))),((0,3),(395,(0,0))),((1,0),(421,(0,0))),((1,4),(530,(0,0))),((2,0),(541,(0,0))),((2,3),(545,(0,0))),((3,1),(546,(0,0))),((3,2),(547,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_167_checked : successorFastRowCheck layer8 row7_167 row7_167choice = true := by decide
def Closure7C020rows : List (List GridPoint) := [row7_160,row7_161,row7_162,row7_163,row7_164,row7_165,row7_166,row7_167]
theorem Closure7C020_closed : ∀ row ∈ Closure7C020rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C020rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_160choice,row7_160_checked⟩
  · subst row
    exact ⟨row7_161choice,row7_161_checked⟩
  · subst row
    exact ⟨row7_162choice,row7_162_checked⟩
  · subst row
    exact ⟨row7_163choice,row7_163_checked⟩
  · subst row
    exact ⟨row7_164choice,row7_164_checked⟩
  · subst row
    exact ⟨row7_165choice,row7_165_checked⟩
  · subst row
    exact ⟨row7_166choice,row7_166_checked⟩
  · subst row
    exact ⟨row7_167choice,row7_167_checked⟩
end Polyomino57
