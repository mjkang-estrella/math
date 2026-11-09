import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_96 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2)]
def row6_96choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(337,(1,0))),((0,-1),(187,(0,1))),((0,1),(145,(0,0))),((1,-1),(471,(0,1))),((1,2),(270,(0,0))),((2,0),(285,(0,0))),((2,2),(297,(0,0))),((3,0),(301,(0,0))),((3,3),(304,(0,0))),((4,1),(305,(0,0))),((4,2),(306,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_96_checked : successorFastRowCheck layer7 row6_96 row6_96choice = true := by decide
def row6_97 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1)]
def row6_97choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(338,(1,0))),((0,-1),(188,(0,1))),((0,1),(146,(0,0))),((1,-1),(472,(0,1))),((1,2),(271,(0,0))),((2,0),(286,(0,0))),((2,2),(298,(0,0))),((3,0),(303,(0,0))),((3,2),(305,(0,0))),((4,0),(307,(0,0))),((4,2),(308,(0,0))),((5,1),(309,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_97_checked : successorFastRowCheck layer7 row6_97 row6_97choice = true := by decide
def row6_98 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2)]
def row6_98choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(339,(1,0))),((0,-1),(189,(0,1))),((0,1),(147,(0,0))),((0,2),(233,(0,0))),((1,-1),(473,(0,1))),((1,1),(258,(0,0))),((1,3),(310,(0,0))),((2,-1),(525,(0,1))),((2,3),(311,(0,0))),((3,0),(312,(0,0))),((3,1),(313,(0,0))),((3,2),(314,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_98_checked : successorFastRowCheck layer7 row6_98 row6_98choice = true := by decide
def row6_99 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3)]
def row6_99choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(340,(1,0))),((0,-1),(198,(0,1))),((0,1),(148,(0,0))),((1,-1),(487,(0,1))),((1,1),(279,(0,0))),((1,2),(311,(0,0))),((1,3),(315,(0,0))),((2,-1),(526,(0,1))),((2,4),(316,(0,0))),((3,0),(317,(0,0))),((3,1),(318,(0,0))),((3,2),(319,(0,0))),((3,3),(320,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_99_checked : successorFastRowCheck layer7 row6_99 row6_99choice = true := by decide
def row6_100 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0)]
def row6_100choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(341,(1,0))),((0,-1),(199,(0,1))),((0,1),(149,(0,0))),((1,-1),(488,(0,1))),((1,1),(280,(0,0))),((1,2),(312,(0,0))),((2,-1),(528,(0,1))),((2,3),(317,(0,0))),((3,-1),(549,(0,1))),((3,1),(321,(0,0))),((3,2),(322,(0,0))),((4,0),(323,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_100_checked : successorFastRowCheck layer7 row6_100 row6_100choice = true := by decide
def row6_101 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1)]
def row6_101choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(342,(1,0))),((0,-1),(200,(0,1))),((0,1),(150,(0,0))),((1,-1),(489,(0,1))),((1,1),(281,(0,0))),((1,2),(313,(0,0))),((2,-1),(529,(0,1))),((2,3),(318,(0,0))),((3,0),(321,(0,0))),((3,2),(324,(0,0))),((4,1),(325,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_101_checked : successorFastRowCheck layer7 row6_101 row6_101choice = true := by decide
def row6_102 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2)]
def row6_102choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(343,(1,0))),((0,-1),(201,(0,1))),((0,1),(151,(0,0))),((1,-1),(490,(0,1))),((1,1),(282,(0,0))),((1,2),(314,(0,0))),((2,-1),(530,(0,1))),((2,3),(319,(0,0))),((3,0),(322,(0,0))),((3,1),(324,(0,0))),((3,3),(326,(0,0))),((4,2),(327,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_102_checked : successorFastRowCheck layer7 row6_102 row6_102choice = true := by decide
def row6_103 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1)]
def row6_103choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(344,(1,0))),((0,-1),(203,(0,1))),((0,1),(152,(0,0))),((1,-1),(492,(0,1))),((1,1),(283,(0,0))),((2,-1),(534,(0,1))),((2,2),(321,(0,0))),((3,-1),(550,(0,1))),((3,2),(328,(0,0))),((4,0),(329,(0,0))),((4,1),(330,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_103_checked : successorFastRowCheck layer7 row6_103 row6_103choice = true := by decide
def Closure6C012rows : List (List GridPoint) := [row6_96,row6_97,row6_98,row6_99,row6_100,row6_101,row6_102,row6_103]
theorem Closure6C012_closed : ∀ row ∈ Closure6C012rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C012rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_96choice,row6_96_checked⟩
  · subst row
    exact ⟨row6_97choice,row6_97_checked⟩
  · subst row
    exact ⟨row6_98choice,row6_98_checked⟩
  · subst row
    exact ⟨row6_99choice,row6_99_checked⟩
  · subst row
    exact ⟨row6_100choice,row6_100_checked⟩
  · subst row
    exact ⟨row6_101choice,row6_101_checked⟩
  · subst row
    exact ⟨row6_102choice,row6_102_checked⟩
  · subst row
    exact ⟨row6_103choice,row6_103_checked⟩
end Polyomino57
