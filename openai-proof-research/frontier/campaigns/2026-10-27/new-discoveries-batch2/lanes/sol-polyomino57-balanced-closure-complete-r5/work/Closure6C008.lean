import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_64 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1)]
def row6_64choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(305,(1,0))),((-1,1),(500,(1,0))),((0,-1),(112,(0,1))),((0,2),(93,(0,0))),((1,0),(142,(0,0))),((1,2),(178,(0,0))),((2,0),(192,(0,0))),((2,3),(199,(0,0))),((3,0),(202,(0,0))),((3,2),(203,(0,0))),((4,1),(204,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_64_checked : successorFastRowCheck layer7 row6_64 row6_64choice = true := by decide
def row6_65 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2)]
def row6_65choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(306,(1,0))),((-1,1),(501,(1,0))),((0,-1),(113,(0,1))),((0,2),(94,(0,0))),((1,0),(143,(0,0))),((1,2),(179,(0,0))),((2,0),(193,(0,0))),((2,3),(200,(0,0))),((3,1),(203,(0,0))),((3,3),(205,(0,0))),((4,2),(206,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_65_checked : successorFastRowCheck layer7 row6_65 row6_65choice = true := by decide
def row6_66 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1)]
def row6_66choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(307,(1,0))),((-1,1),(502,(1,0))),((0,-1),(114,(0,1))),((0,2),(95,(0,0))),((1,0),(144,(0,0))),((1,2),(180,(0,0))),((2,0),(194,(0,0))),((2,2),(202,(0,0))),((3,-1),(427,(0,1))),((3,2),(207,(0,0))),((4,0),(208,(0,0))),((4,1),(209,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_66_checked : successorFastRowCheck layer7 row6_66 row6_66choice = true := by decide
def row6_67 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2)]
def row6_67choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(308,(1,0))),((-1,1),(503,(1,0))),((0,-1),(115,(0,1))),((0,2),(96,(0,0))),((1,0),(145,(0,0))),((1,2),(181,(0,0))),((2,0),(196,(0,0))),((2,2),(203,(0,0))),((3,0),(207,(0,0))),((3,3),(210,(0,0))),((4,1),(211,(0,0))),((4,2),(212,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_67_checked : successorFastRowCheck layer7 row6_67 row6_67choice = true := by decide
def row6_68 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1)]
def row6_68choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(309,(1,0))),((-1,1),(504,(1,0))),((0,-1),(116,(0,1))),((0,2),(97,(0,0))),((1,0),(146,(0,0))),((1,2),(182,(0,0))),((2,0),(197,(0,0))),((2,2),(204,(0,0))),((3,0),(209,(0,0))),((3,2),(211,(0,0))),((4,0),(213,(0,0))),((4,2),(214,(0,0))),((5,1),(215,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_68_checked : successorFastRowCheck layer7 row6_68 row6_68choice = true := by decide
def row6_69 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2)]
def row6_69choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(310,(1,0))),((-1,2),(639,(1,0))),((-1,3),(723,(1,0))),((0,-1),(117,(0,1))),((0,1),(23,(0,0))),((0,4),(216,(0,0))),((1,-1),(428,(0,1))),((1,3),(217,(0,0))),((2,0),(218,(0,0))),((2,1),(219,(0,0))),((2,2),(220,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_69_checked : successorFastRowCheck layer7 row6_69 row6_69choice = true := by decide
def row6_70 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3)]
def row6_70choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(311,(1,0))),((-1,2),(640,(1,0))),((0,-1),(119,(0,1))),((0,1),(57,(0,0))),((0,3),(217,(0,0))),((1,-1),(429,(0,1))),((1,4),(221,(0,0))),((2,0),(222,(0,0))),((2,1),(223,(0,0))),((2,2),(224,(0,0))),((2,3),(225,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_70_checked : successorFastRowCheck layer7 row6_70 row6_70choice = true := by decide
def row6_71 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0)]
def row6_71choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(312,(1,0))),((-1,2),(641,(1,0))),((0,-1),(120,(0,1))),((0,1),(58,(0,0))),((0,3),(218,(0,0))),((1,-1),(431,(0,1))),((1,3),(222,(0,0))),((2,-1),(434,(0,1))),((2,1),(226,(0,0))),((2,2),(227,(0,0))),((3,0),(228,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_71_checked : successorFastRowCheck layer7 row6_71 row6_71choice = true := by decide
def Closure6C008rows : List (List GridPoint) := [row6_64,row6_65,row6_66,row6_67,row6_68,row6_69,row6_70,row6_71]
theorem Closure6C008_closed : ∀ row ∈ Closure6C008rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C008rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_64choice,row6_64_checked⟩
  · subst row
    exact ⟨row6_65choice,row6_65_checked⟩
  · subst row
    exact ⟨row6_66choice,row6_66_checked⟩
  · subst row
    exact ⟨row6_67choice,row6_67_checked⟩
  · subst row
    exact ⟨row6_68choice,row6_68_checked⟩
  · subst row
    exact ⟨row6_69choice,row6_69_checked⟩
  · subst row
    exact ⟨row6_70choice,row6_70_checked⟩
  · subst row
    exact ⟨row6_71choice,row6_71_checked⟩
end Polyomino57
