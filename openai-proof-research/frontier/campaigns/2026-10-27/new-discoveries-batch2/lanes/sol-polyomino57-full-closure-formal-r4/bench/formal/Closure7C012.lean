import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_96 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2)]
def row7_96choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(889,(1,0))),((-1,1),(1555,(1,0))),((-1,2),(2143,(1,0))),((0,-1),(165,(0,1))),((0,3),(146,(0,0))),((1,0),(215,(0,0))),((1,2),(281,(0,0))),((2,0),(296,(0,0))),((2,2),(303,(0,0))),((3,0),(307,(0,0))),((3,3),(310,(0,0))),((4,1),(311,(0,0))),((4,2),(312,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_96_checked : successorFastRowCheck layer8 row7_96 row7_96choice = true := by decide
def row7_97 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1)]
def row7_97choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(890,(1,0))),((-1,1),(1556,(1,0))),((-1,2),(2144,(1,0))),((0,-1),(166,(0,1))),((0,3),(147,(0,0))),((1,0),(216,(0,0))),((1,2),(282,(0,0))),((2,0),(297,(0,0))),((2,2),(304,(0,0))),((3,0),(309,(0,0))),((3,2),(311,(0,0))),((4,0),(313,(0,0))),((4,2),(314,(0,0))),((5,1),(315,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_97_checked : successorFastRowCheck layer8 row7_97 row7_97choice = true := by decide
def row7_98 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5)]
def row7_98choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(891,(1,0))),((-1,1),(1557,(1,0))),((-1,2),(2145,(1,0))),((0,-1),(167,(0,1))),((0,3),(148,(0,0))),((0,4),(189,(0,0))),((0,5),(193,(0,0))),((1,0),(217,(0,0))),((1,1),(261,(0,0))),((1,6),(316,(0,0))),((2,2),(317,(0,0))),((2,3),(318,(0,0))),((2,4),(319,(0,0))),((2,5),(320,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_98_checked : successorFastRowCheck layer8 row7_98 row7_98choice = true := by decide
def row7_99 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2)]
def row7_99choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(892,(1,0))),((-1,1),(1558,(1,0))),((-1,2),(2146,(1,0))),((0,-1),(168,(0,1))),((0,3),(149,(0,0))),((0,4),(190,(0,0))),((1,0),(219,(0,0))),((1,1),(263,(0,0))),((1,5),(317,(0,0))),((2,1),(321,(0,0))),((2,3),(322,(0,0))),((2,4),(323,(0,0))),((3,2),(324,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_99_checked : successorFastRowCheck layer8 row7_99 row7_99choice = true := by decide
def row7_100 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3)]
def row7_100choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(893,(1,0))),((-1,1),(1559,(1,0))),((-1,2),(2147,(1,0))),((0,-1),(169,(0,1))),((0,3),(150,(0,0))),((0,4),(191,(0,0))),((1,0),(220,(0,0))),((1,1),(264,(0,0))),((1,5),(318,(0,0))),((2,2),(322,(0,0))),((2,4),(325,(0,0))),((3,3),(326,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_100_checked : successorFastRowCheck layer8 row7_100 row7_100choice = true := by decide
def row7_101 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4)]
def row7_101choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(894,(1,0))),((-1,1),(1560,(1,0))),((-1,2),(2148,(1,0))),((0,-1),(170,(0,1))),((0,3),(151,(0,0))),((0,4),(192,(0,0))),((1,0),(221,(0,0))),((1,1),(265,(0,0))),((1,5),(319,(0,0))),((2,2),(323,(0,0))),((2,3),(325,(0,0))),((2,5),(327,(0,0))),((3,4),(328,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_101_checked : successorFastRowCheck layer8 row7_101 row7_101choice = true := by decide
def row7_102 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2)]
def row7_102choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(895,(1,0))),((-1,1),(1561,(1,0))),((-1,2),(2149,(1,0))),((0,-1),(171,(0,1))),((0,3),(152,(0,0))),((1,0),(226,(0,0))),((1,1),(267,(0,0))),((1,4),(321,(0,0))),((2,0),(329,(0,0))),((2,3),(330,(0,0))),((3,1),(331,(0,0))),((3,2),(332,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_102_checked : successorFastRowCheck layer8 row7_102 row7_102choice = true := by decide
def row7_103 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3)]
def row7_103choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(896,(1,0))),((-1,1),(1562,(1,0))),((-1,2),(2150,(1,0))),((0,-1),(172,(0,1))),((0,3),(153,(0,0))),((1,0),(227,(0,0))),((1,1),(270,(0,0))),((1,4),(322,(0,0))),((2,1),(330,(0,0))),((2,4),(333,(0,0))),((3,2),(334,(0,0))),((3,3),(335,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_103_checked : successorFastRowCheck layer8 row7_103 row7_103choice = true := by decide
def Closure7C012rows : List (List GridPoint) := [row7_96,row7_97,row7_98,row7_99,row7_100,row7_101,row7_102,row7_103]
theorem Closure7C012_closed : ∀ row ∈ Closure7C012rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C012rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_96choice,row7_96_checked⟩
  · subst row
    exact ⟨row7_97choice,row7_97_checked⟩
  · subst row
    exact ⟨row7_98choice,row7_98_checked⟩
  · subst row
    exact ⟨row7_99choice,row7_99_checked⟩
  · subst row
    exact ⟨row7_100choice,row7_100_checked⟩
  · subst row
    exact ⟨row7_101choice,row7_101_checked⟩
  · subst row
    exact ⟨row7_102choice,row7_102_checked⟩
  · subst row
    exact ⟨row7_103choice,row7_103_checked⟩
end Polyomino57
