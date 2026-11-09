import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_240 : List GridPoint := [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row7_240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1033,(1,0))),((-1,4),(2672,(1,0))),((0,-1),(410,(0,1))),((0,1),(404,(0,0))),((0,2),(716,(0,0))),((0,3),(760,(0,0))),((0,5),(785,(0,0))),((1,-1),(1458,(0,1))),((1,5),(786,(0,0))),((2,0),(787,(0,0))),((2,1),(788,(0,0))),((2,2),(789,(0,0))),((2,3),(790,(0,0))),((2,4),(791,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_240_checked : successorFastRowCheck layer8 row7_240 row7_240choice = true := by decide
def row7_241 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def row7_241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1034,(1,0))),((0,-1),(523,(0,1))),((0,1),(411,(0,0))),((0,2),(717,(0,0))),((0,3),(765,(0,0))),((0,4),(786,(0,0))),((0,5),(792,(0,0))),((1,-1),(1459,(0,1))),((1,6),(793,(0,0))),((2,0),(794,(0,0))),((2,1),(795,(0,0))),((2,2),(796,(0,0))),((2,3),(797,(0,0))),((2,4),(798,(0,0))),((2,5),(799,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_241_checked : successorFastRowCheck layer8 row7_241 row7_241choice = true := by decide
def row7_242 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def row7_242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1035,(1,0))),((0,-1),(524,(0,1))),((0,1),(412,(0,0))),((0,2),(718,(0,0))),((0,3),(766,(0,0))),((0,4),(787,(0,0))),((1,-1),(1461,(0,1))),((1,5),(794,(0,0))),((2,-1),(1675,(0,1))),((2,1),(800,(0,0))),((2,2),(801,(0,0))),((2,3),(802,(0,0))),((2,4),(803,(0,0))),((3,0),(804,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_242_checked : successorFastRowCheck layer8 row7_242 row7_242choice = true := by decide
def row7_243 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def row7_243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1036,(1,0))),((0,-1),(525,(0,1))),((0,1),(413,(0,0))),((0,2),(719,(0,0))),((0,3),(767,(0,0))),((0,4),(788,(0,0))),((1,-1),(1462,(0,1))),((1,5),(795,(0,0))),((2,0),(800,(0,0))),((2,2),(805,(0,0))),((2,3),(806,(0,0))),((2,4),(807,(0,0))),((3,1),(808,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_243_checked : successorFastRowCheck layer8 row7_243 row7_243choice = true := by decide
def row7_244 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def row7_244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1037,(1,0))),((0,-1),(526,(0,1))),((0,1),(414,(0,0))),((0,2),(720,(0,0))),((0,3),(768,(0,0))),((0,4),(789,(0,0))),((1,-1),(1463,(0,1))),((1,5),(796,(0,0))),((2,0),(801,(0,0))),((2,1),(805,(0,0))),((2,3),(809,(0,0))),((2,4),(810,(0,0))),((3,2),(811,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_244_checked : successorFastRowCheck layer8 row7_244 row7_244choice = true := by decide
def row7_245 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def row7_245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1038,(1,0))),((0,-1),(527,(0,1))),((0,1),(415,(0,0))),((0,2),(721,(0,0))),((0,3),(769,(0,0))),((0,4),(790,(0,0))),((1,-1),(1464,(0,1))),((1,5),(797,(0,0))),((2,0),(802,(0,0))),((2,1),(806,(0,0))),((2,2),(809,(0,0))),((2,4),(812,(0,0))),((3,3),(813,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_245_checked : successorFastRowCheck layer8 row7_245 row7_245choice = true := by decide
def row7_246 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def row7_246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1039,(1,0))),((0,-1),(528,(0,1))),((0,1),(416,(0,0))),((0,2),(722,(0,0))),((0,3),(770,(0,0))),((0,4),(791,(0,0))),((1,-1),(1465,(0,1))),((1,5),(798,(0,0))),((2,0),(803,(0,0))),((2,1),(807,(0,0))),((2,2),(810,(0,0))),((2,3),(812,(0,0))),((2,5),(814,(0,0))),((3,4),(815,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_246_checked : successorFastRowCheck layer8 row7_246 row7_246choice = true := by decide
def row7_247 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def row7_247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(1040,(1,0))),((0,-1),(530,(0,1))),((0,1),(417,(0,0))),((0,2),(723,(0,0))),((0,3),(771,(0,0))),((1,-1),(1471,(0,1))),((1,4),(800,(0,0))),((2,-1),(1676,(0,1))),((2,2),(816,(0,0))),((2,3),(817,(0,0))),((3,0),(818,(0,0))),((3,1),(819,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_247_checked : successorFastRowCheck layer8 row7_247 row7_247choice = true := by decide
def Closure7C030rows : List (List GridPoint) := [row7_240,row7_241,row7_242,row7_243,row7_244,row7_245,row7_246,row7_247]
theorem Closure7C030_closed : ∀ row ∈ Closure7C030rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C030rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_240choice,row7_240_checked⟩
  · subst row
    exact ⟨row7_241choice,row7_241_checked⟩
  · subst row
    exact ⟨row7_242choice,row7_242_checked⟩
  · subst row
    exact ⟨row7_243choice,row7_243_checked⟩
  · subst row
    exact ⟨row7_244choice,row7_244_checked⟩
  · subst row
    exact ⟨row7_245choice,row7_245_checked⟩
  · subst row
    exact ⟨row7_246choice,row7_246_checked⟩
  · subst row
    exact ⟨row7_247choice,row7_247_checked⟩
end Polyomino57
