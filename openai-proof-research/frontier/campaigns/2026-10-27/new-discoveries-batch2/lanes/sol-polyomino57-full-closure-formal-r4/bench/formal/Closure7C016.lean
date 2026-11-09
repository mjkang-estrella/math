import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_128 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row7_128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(921,(1,0))),((-1,1),(1587,(1,0))),((0,-1),(265,(0,1))),((0,2),(198,(0,0))),((0,3),(388,(0,0))),((1,-1),(1255,(0,1))),((1,4),(415,(0,0))),((2,0),(419,(0,0))),((2,1),(422,(0,0))),((2,2),(424,(0,0))),((2,4),(426,(0,0))),((3,3),(427,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_128_checked : successorFastRowCheck layer8 row7_128 row7_128choice = true := by decide
def row7_129 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row7_129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(922,(1,0))),((-1,1),(1588,(1,0))),((0,-1),(267,(0,1))),((0,2),(199,(0,0))),((1,-1),(1260,(0,1))),((1,3),(417,(0,0))),((2,-1),(1325,(0,1))),((2,2),(428,(0,0))),((3,0),(429,(0,0))),((3,1),(430,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_129_checked : successorFastRowCheck layer8 row7_129 row7_129choice = true := by decide
def row7_130 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row7_130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(923,(1,0))),((-1,1),(1589,(1,0))),((0,-1),(268,(0,1))),((0,2),(200,(0,0))),((1,-1),(1261,(0,1))),((1,3),(418,(0,0))),((2,-1),(1326,(0,1))),((2,1),(428,(0,0))),((2,3),(431,(0,0))),((3,0),(432,(0,0))),((3,2),(433,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_130_checked : successorFastRowCheck layer8 row7_130 row7_130choice = true := by decide
def row7_131 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row7_131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(924,(1,0))),((-1,1),(1590,(1,0))),((0,-1),(269,(0,1))),((0,2),(201,(0,0))),((1,-1),(1262,(0,1))),((1,3),(420,(0,0))),((2,-1),(1328,(0,1))),((2,1),(429,(0,0))),((2,2),(432,(0,0))),((3,-1),(1329,(0,1))),((3,1),(434,(0,0))),((4,0),(435,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_131_checked : successorFastRowCheck layer8 row7_131 row7_131choice = true := by decide
def row7_132 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row7_132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(925,(1,0))),((-1,1),(1591,(1,0))),((0,-1),(270,(0,1))),((0,2),(202,(0,0))),((1,-1),(1263,(0,1))),((1,3),(421,(0,0))),((2,0),(428,(0,0))),((2,3),(436,(0,0))),((3,1),(437,(0,0))),((3,2),(438,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_132_checked : successorFastRowCheck layer8 row7_132 row7_132choice = true := by decide
def row7_133 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row7_133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(926,(1,0))),((-1,1),(1592,(1,0))),((0,-1),(271,(0,1))),((0,2),(203,(0,0))),((1,-1),(1264,(0,1))),((1,3),(423,(0,0))),((2,0),(430,(0,0))),((2,2),(437,(0,0))),((3,0),(439,(0,0))),((3,2),(440,(0,0))),((4,1),(441,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_133_checked : successorFastRowCheck layer8 row7_133 row7_133choice = true := by decide
def row7_134 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row7_134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(927,(1,0))),((-1,1),(1593,(1,0))),((0,-1),(272,(0,1))),((0,2),(204,(0,0))),((1,-1),(1265,(0,1))),((1,3),(424,(0,0))),((2,0),(431,(0,0))),((2,1),(436,(0,0))),((2,4),(442,(0,0))),((3,2),(443,(0,0))),((3,3),(444,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_134_checked : successorFastRowCheck layer8 row7_134 row7_134choice = true := by decide
def row7_135 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row7_135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(928,(1,0))),((-1,1),(1594,(1,0))),((0,-1),(273,(0,1))),((0,2),(205,(0,0))),((1,-1),(1266,(0,1))),((1,3),(425,(0,0))),((2,0),(433,(0,0))),((2,1),(438,(0,0))),((2,3),(443,(0,0))),((3,1),(445,(0,0))),((3,3),(446,(0,0))),((4,2),(447,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_135_checked : successorFastRowCheck layer8 row7_135 row7_135choice = true := by decide
def Closure7C016rows : List (List GridPoint) := [row7_128,row7_129,row7_130,row7_131,row7_132,row7_133,row7_134,row7_135]
theorem Closure7C016_closed : ∀ row ∈ Closure7C016rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C016rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_128choice,row7_128_checked⟩
  · subst row
    exact ⟨row7_129choice,row7_129_checked⟩
  · subst row
    exact ⟨row7_130choice,row7_130_checked⟩
  · subst row
    exact ⟨row7_131choice,row7_131_checked⟩
  · subst row
    exact ⟨row7_132choice,row7_132_checked⟩
  · subst row
    exact ⟨row7_133choice,row7_133_checked⟩
  · subst row
    exact ⟨row7_134choice,row7_134_checked⟩
  · subst row
    exact ⟨row7_135choice,row7_135_checked⟩
end Polyomino57
