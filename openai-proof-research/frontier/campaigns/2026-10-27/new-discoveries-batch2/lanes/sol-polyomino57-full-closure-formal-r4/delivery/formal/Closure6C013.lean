import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_104 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0)]
def row6_104choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(345,(1,0))),((0,-1),(204,(0,1))),((0,1),(153,(0,0))),((1,-1),(493,(0,1))),((1,1),(284,(0,0))),((2,-1),(535,(0,1))),((2,2),(323,(0,0))),((3,-1),(552,(0,1))),((3,1),(329,(0,0))),((4,-1),(553,(0,1))),((4,1),(331,(0,0))),((5,0),(332,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_104_checked : successorFastRowCheck layer7 row6_104 row6_104choice = true := by decide
def row6_105 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2)]
def row6_105choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(346,(1,0))),((0,-1),(205,(0,1))),((0,1),(154,(0,0))),((1,-1),(494,(0,1))),((1,1),(285,(0,0))),((2,-1),(536,(0,1))),((2,2),(324,(0,0))),((3,0),(328,(0,0))),((3,3),(333,(0,0))),((4,1),(334,(0,0))),((4,2),(335,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_105_checked : successorFastRowCheck layer7 row6_105 row6_105choice = true := by decide
def row6_106 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1)]
def row6_106choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(347,(1,0))),((0,-1),(206,(0,1))),((0,1),(155,(0,0))),((1,-1),(495,(0,1))),((1,1),(286,(0,0))),((2,-1),(537,(0,1))),((2,2),(325,(0,0))),((3,0),(330,(0,0))),((3,2),(334,(0,0))),((4,0),(336,(0,0))),((4,2),(337,(0,0))),((5,1),(338,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_106_checked : successorFastRowCheck layer7 row6_106 row6_106choice = true := by decide
def row6_107 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2)]
def row6_107choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(348,(1,0))),((0,-1),(210,(0,1))),((0,1),(156,(0,0))),((1,-1),(499,(0,1))),((1,1),(287,(0,0))),((2,-1),(543,(0,1))),((2,1),(328,(0,0))),((2,2),(339,(0,0))),((3,-1),(554,(0,1))),((3,3),(340,(0,0))),((4,0),(341,(0,0))),((4,1),(342,(0,0))),((4,2),(343,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_107_checked : successorFastRowCheck layer7 row6_107 row6_107choice = true := by decide
def row6_108 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0)]
def row6_108choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(349,(1,0))),((0,-1),(211,(0,1))),((0,1),(157,(0,0))),((1,-1),(500,(0,1))),((1,1),(288,(0,0))),((2,-1),(544,(0,1))),((2,1),(329,(0,0))),((3,-1),(556,(0,1))),((3,2),(341,(0,0))),((4,-1),(562,(0,1))),((4,1),(344,(0,0))),((5,0),(345,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_108_checked : successorFastRowCheck layer7 row6_108 row6_108choice = true := by decide
def row6_109 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
def row6_109choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(350,(1,0))),((0,-1),(212,(0,1))),((0,1),(158,(0,0))),((1,-1),(501,(0,1))),((1,1),(289,(0,0))),((2,-1),(545,(0,1))),((2,1),(330,(0,0))),((3,-1),(557,(0,1))),((3,2),(342,(0,0))),((4,0),(344,(0,0))),((4,2),(346,(0,0))),((5,1),(347,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_109_checked : successorFastRowCheck layer7 row6_109 row6_109choice = true := by decide
def row6_110 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1)]
def row6_110choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(351,(1,0))),((0,-1),(214,(0,1))),((0,1),(159,(0,0))),((1,-1),(503,(0,1))),((1,1),(290,(0,0))),((2,-1),(547,(0,1))),((2,1),(331,(0,0))),((3,-1),(560,(0,1))),((3,1),(344,(0,0))),((4,-1),(563,(0,1))),((4,2),(348,(0,0))),((5,0),(349,(0,0))),((5,1),(350,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_110_checked : successorFastRowCheck layer7 row6_110 row6_110choice = true := by decide
def row6_111 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0)]
def row6_111choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(352,(1,0))),((0,-1),(215,(0,1))),((0,1),(160,(0,0))),((1,-1),(504,(0,1))),((1,1),(291,(0,0))),((2,-1),(548,(0,1))),((2,1),(332,(0,0))),((3,-1),(561,(0,1))),((3,1),(345,(0,0))),((4,-1),(565,(0,1))),((4,1),(349,(0,0))),((5,-1),(566,(0,1))),((5,1),(351,(0,0))),((6,0),(352,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_111_checked : successorFastRowCheck layer7 row6_111 row6_111choice = true := by decide
def Closure6C013rows : List (List GridPoint) := [row6_104,row6_105,row6_106,row6_107,row6_108,row6_109,row6_110,row6_111]
theorem Closure6C013_closed : ∀ row ∈ Closure6C013rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C013rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_104choice,row6_104_checked⟩
  · subst row
    exact ⟨row6_105choice,row6_105_checked⟩
  · subst row
    exact ⟨row6_106choice,row6_106_checked⟩
  · subst row
    exact ⟨row6_107choice,row6_107_checked⟩
  · subst row
    exact ⟨row6_108choice,row6_108_checked⟩
  · subst row
    exact ⟨row6_109choice,row6_109_checked⟩
  · subst row
    exact ⟨row6_110choice,row6_110_checked⟩
  · subst row
    exact ⟨row6_111choice,row6_111_checked⟩
end Polyomino57
