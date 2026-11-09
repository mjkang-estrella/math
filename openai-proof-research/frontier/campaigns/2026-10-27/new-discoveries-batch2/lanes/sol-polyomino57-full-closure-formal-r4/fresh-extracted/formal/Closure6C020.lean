import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_160 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row6_160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(553,(1,0))),((0,0),(180,(0,0))),((0,2),(407,(0,0))),((1,0),(464,(0,0))),((1,3),(510,(0,0))),((2,0),(515,(0,0))),((2,2),(519,(0,0))),((3,-1),(670,(0,1))),((3,2),(520,(0,0))),((4,0),(521,(0,0))),((4,1),(522,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_160_checked : successorFastRowCheck layer7 row6_160 row6_160choice = true := by decide
def row6_161 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3)]
def row6_161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(554,(1,0))),((0,0),(190,(0,0))),((0,2),(408,(0,0))),((1,0),(474,(0,0))),((1,2),(511,(0,0))),((1,3),(525,(0,0))),((2,-1),(671,(0,1))),((2,4),(526,(0,0))),((3,0),(527,(0,0))),((3,1),(528,(0,0))),((3,2),(529,(0,0))),((3,3),(530,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_161_checked : successorFastRowCheck layer7 row6_161 row6_161choice = true := by decide
def row6_162 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0)]
def row6_162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(555,(1,0))),((0,0),(191,(0,0))),((0,2),(409,(0,0))),((1,0),(475,(0,0))),((1,2),(512,(0,0))),((2,-1),(673,(0,1))),((2,3),(527,(0,0))),((3,-1),(684,(0,1))),((3,1),(531,(0,0))),((3,2),(532,(0,0))),((4,0),(533,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_162_checked : successorFastRowCheck layer7 row6_162 row6_162choice = true := by decide
def row6_163 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1)]
def row6_163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(556,(1,0))),((0,0),(192,(0,0))),((0,2),(410,(0,0))),((1,0),(476,(0,0))),((1,2),(513,(0,0))),((2,-1),(674,(0,1))),((2,3),(528,(0,0))),((3,0),(531,(0,0))),((3,2),(534,(0,0))),((4,1),(535,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_163_checked : successorFastRowCheck layer7 row6_163 row6_163choice = true := by decide
def row6_164 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2)]
def row6_164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(557,(1,0))),((0,0),(193,(0,0))),((0,2),(411,(0,0))),((1,0),(477,(0,0))),((1,2),(514,(0,0))),((2,-1),(675,(0,1))),((2,3),(529,(0,0))),((3,0),(532,(0,0))),((3,1),(534,(0,0))),((3,3),(536,(0,0))),((4,2),(537,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_164_checked : successorFastRowCheck layer7 row6_164 row6_164choice = true := by decide
def row6_165 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1)]
def row6_165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(558,(1,0))),((0,0),(194,(0,0))),((0,2),(412,(0,0))),((1,0),(478,(0,0))),((1,2),(515,(0,0))),((2,-1),(679,(0,1))),((2,2),(531,(0,0))),((3,-1),(685,(0,1))),((3,2),(538,(0,0))),((4,0),(539,(0,0))),((4,1),(540,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_165_checked : successorFastRowCheck layer7 row6_165 row6_165choice = true := by decide
def row6_166 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(4,0)]
def row6_166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(559,(1,0))),((0,0),(195,(0,0))),((0,2),(413,(0,0))),((1,0),(479,(0,0))),((1,2),(516,(0,0))),((2,-1),(680,(0,1))),((2,2),(533,(0,0))),((3,-1),(687,(0,1))),((3,1),(539,(0,0))),((4,-1),(688,(0,1))),((4,1),(541,(0,0))),((5,0),(542,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_166_checked : successorFastRowCheck layer7 row6_166 row6_166choice = true := by decide
def row6_167 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2)]
def row6_167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(560,(1,0))),((0,0),(196,(0,0))),((0,2),(414,(0,0))),((1,0),(480,(0,0))),((1,2),(517,(0,0))),((2,-1),(681,(0,1))),((2,2),(534,(0,0))),((3,0),(538,(0,0))),((3,3),(543,(0,0))),((4,1),(544,(0,0))),((4,2),(545,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_167_checked : successorFastRowCheck layer7 row6_167 row6_167choice = true := by decide
def Closure6C020rows : List (List GridPoint) := [row6_160,row6_161,row6_162,row6_163,row6_164,row6_165,row6_166,row6_167]
theorem Closure6C020_closed : ∀ row ∈ Closure6C020rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C020rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_160choice,row6_160_checked⟩
  · subst row
    exact ⟨row6_161choice,row6_161_checked⟩
  · subst row
    exact ⟨row6_162choice,row6_162_checked⟩
  · subst row
    exact ⟨row6_163choice,row6_163_checked⟩
  · subst row
    exact ⟨row6_164choice,row6_164_checked⟩
  · subst row
    exact ⟨row6_165choice,row6_165_checked⟩
  · subst row
    exact ⟨row6_166choice,row6_166_checked⟩
  · subst row
    exact ⟨row6_167choice,row6_167_checked⟩
end Polyomino57
