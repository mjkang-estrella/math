import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_64 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1)]
def row7_64choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(857,(1,0))),((-1,1),(1523,(1,0))),((-1,2),(2111,(1,0))),((0,-1),(127,(0,1))),((0,3),(93,(0,0))),((1,-1),(1190,(0,1))),((1,2),(203,(0,0))),((2,0),(208,(0,0))),((2,2),(212,(0,0))),((3,0),(214,(0,0))),((3,2),(215,(0,0))),((4,1),(216,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_64_checked : successorFastRowCheck layer8 row7_64 row7_64choice = true := by decide
def row7_65 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4)]
def row7_65choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(858,(1,0))),((-1,1),(1524,(1,0))),((-1,2),(2112,(1,0))),((0,-1),(128,(0,1))),((0,3),(94,(0,0))),((0,4),(187,(0,0))),((1,-1),(1191,(0,1))),((1,1),(194,(0,0))),((1,5),(217,(0,0))),((2,0),(218,(0,0))),((2,2),(219,(0,0))),((2,3),(220,(0,0))),((2,4),(221,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_65_checked : successorFastRowCheck layer8 row7_65 row7_65choice = true := by decide
def row7_66 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0)]
def row7_66choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(859,(1,0))),((-1,1),(1525,(1,0))),((-1,2),(2113,(1,0))),((0,-1),(129,(0,1))),((0,3),(95,(0,0))),((1,-1),(1193,(0,1))),((1,1),(195,(0,0))),((1,4),(218,(0,0))),((2,-1),(1222,(0,1))),((2,1),(222,(0,0))),((2,2),(223,(0,0))),((2,3),(224,(0,0))),((3,0),(225,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_66_checked : successorFastRowCheck layer8 row7_66 row7_66choice = true := by decide
def row7_67 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2)]
def row7_67choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(860,(1,0))),((-1,1),(1526,(1,0))),((-1,2),(2114,(1,0))),((0,-1),(130,(0,1))),((0,3),(96,(0,0))),((1,-1),(1194,(0,1))),((1,1),(197,(0,0))),((1,4),(219,(0,0))),((2,0),(223,(0,0))),((2,1),(226,(0,0))),((2,3),(227,(0,0))),((3,2),(228,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_67_checked : successorFastRowCheck layer8 row7_67 row7_67choice = true := by decide
def row7_68 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3)]
def row7_68choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(861,(1,0))),((-1,1),(1527,(1,0))),((-1,2),(2115,(1,0))),((0,-1),(131,(0,1))),((0,3),(97,(0,0))),((1,-1),(1195,(0,1))),((1,1),(198,(0,0))),((1,4),(220,(0,0))),((2,0),(224,(0,0))),((2,2),(227,(0,0))),((2,4),(229,(0,0))),((3,3),(230,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_68_checked : successorFastRowCheck layer8 row7_68 row7_68choice = true := by decide
def row7_69 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
def row7_69choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(862,(1,0))),((-1,1),(1528,(1,0))),((-1,2),(2116,(1,0))),((0,-1),(133,(0,1))),((0,3),(98,(0,0))),((1,-1),(1199,(0,1))),((1,1),(199,(0,0))),((1,3),(222,(0,0))),((2,-1),(1223,(0,1))),((2,2),(231,(0,0))),((3,0),(232,(0,0))),((3,1),(233,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_69_checked : successorFastRowCheck layer8 row7_69 row7_69choice = true := by decide
def row7_70 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2)]
def row7_70choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(863,(1,0))),((-1,1),(1529,(1,0))),((-1,2),(2117,(1,0))),((0,-1),(134,(0,1))),((0,3),(99,(0,0))),((1,-1),(1200,(0,1))),((1,1),(200,(0,0))),((1,3),(223,(0,0))),((2,-1),(1224,(0,1))),((2,1),(231,(0,0))),((2,3),(234,(0,0))),((3,0),(235,(0,0))),((3,2),(236,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_70_checked : successorFastRowCheck layer8 row7_70 row7_70choice = true := by decide
def row7_71 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0)]
def row7_71choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(864,(1,0))),((-1,1),(1530,(1,0))),((-1,2),(2118,(1,0))),((0,-1),(135,(0,1))),((0,3),(100,(0,0))),((1,-1),(1201,(0,1))),((1,1),(201,(0,0))),((1,3),(225,(0,0))),((2,-1),(1226,(0,1))),((2,1),(232,(0,0))),((2,2),(235,(0,0))),((3,-1),(1227,(0,1))),((3,1),(237,(0,0))),((4,0),(238,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_71_checked : successorFastRowCheck layer8 row7_71 row7_71choice = true := by decide
def Closure7C008rows : List (List GridPoint) := [row7_64,row7_65,row7_66,row7_67,row7_68,row7_69,row7_70,row7_71]
theorem Closure7C008_closed : ∀ row ∈ Closure7C008rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C008rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_64choice,row7_64_checked⟩
  · subst row
    exact ⟨row7_65choice,row7_65_checked⟩
  · subst row
    exact ⟨row7_66choice,row7_66_checked⟩
  · subst row
    exact ⟨row7_67choice,row7_67_checked⟩
  · subst row
    exact ⟨row7_68choice,row7_68_checked⟩
  · subst row
    exact ⟨row7_69choice,row7_69_checked⟩
  · subst row
    exact ⟨row7_70choice,row7_70_checked⟩
  · subst row
    exact ⟨row7_71choice,row7_71_checked⟩
end Polyomino57
