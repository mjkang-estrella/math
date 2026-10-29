import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_72 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1)]
def row6_72choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(313,(1,0))),((-1,2),(642,(1,0))),((0,-1),(121,(0,1))),((0,1),(59,(0,0))),((0,3),(219,(0,0))),((1,-1),(432,(0,1))),((1,3),(223,(0,0))),((2,0),(226,(0,0))),((2,2),(229,(0,0))),((3,1),(230,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_72_checked : successorFastRowCheck layer7 row6_72 row6_72choice = true := by decide
def row6_73 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2)]
def row6_73choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(314,(1,0))),((-1,2),(643,(1,0))),((0,-1),(122,(0,1))),((0,1),(60,(0,0))),((0,3),(220,(0,0))),((1,-1),(433,(0,1))),((1,3),(224,(0,0))),((2,0),(227,(0,0))),((2,1),(229,(0,0))),((2,3),(231,(0,0))),((3,2),(232,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_73_checked : successorFastRowCheck layer7 row6_73 row6_73choice = true := by decide
def row6_74 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row6_74choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(315,(1,0))),((-1,3),(724,(1,0))),((0,-1),(123,(0,1))),((0,1),(118,(0,0))),((0,2),(217,(0,0))),((0,4),(234,(0,0))),((1,-1),(435,(0,1))),((1,4),(235,(0,0))),((2,0),(236,(0,0))),((2,1),(237,(0,0))),((2,2),(238,(0,0))),((2,3),(239,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_74_checked : successorFastRowCheck layer7 row6_74 row6_74choice = true := by decide
def row6_75 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4)]
def row6_75choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(316,(1,0))),((0,-1),(161,(0,1))),((0,1),(124,(0,0))),((0,2),(221,(0,0))),((0,3),(235,(0,0))),((0,4),(240,(0,0))),((1,-1),(436,(0,1))),((1,5),(241,(0,0))),((2,0),(242,(0,0))),((2,1),(243,(0,0))),((2,2),(244,(0,0))),((2,3),(245,(0,0))),((2,4),(246,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_75_checked : successorFastRowCheck layer7 row6_75 row6_75choice = true := by decide
def row6_76 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0)]
def row6_76choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(317,(1,0))),((0,-1),(162,(0,1))),((0,1),(125,(0,0))),((0,2),(222,(0,0))),((0,3),(236,(0,0))),((1,-1),(438,(0,1))),((1,4),(242,(0,0))),((2,-1),(505,(0,1))),((2,1),(247,(0,0))),((2,2),(248,(0,0))),((2,3),(249,(0,0))),((3,0),(250,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_76_checked : successorFastRowCheck layer7 row6_76 row6_76choice = true := by decide
def row6_77 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1)]
def row6_77choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(318,(1,0))),((0,-1),(163,(0,1))),((0,1),(126,(0,0))),((0,2),(223,(0,0))),((0,3),(237,(0,0))),((1,-1),(439,(0,1))),((1,4),(243,(0,0))),((2,0),(247,(0,0))),((2,2),(251,(0,0))),((2,3),(252,(0,0))),((3,1),(253,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_77_checked : successorFastRowCheck layer7 row6_77 row6_77choice = true := by decide
def row6_78 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2)]
def row6_78choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(319,(1,0))),((0,-1),(164,(0,1))),((0,1),(127,(0,0))),((0,2),(224,(0,0))),((0,3),(238,(0,0))),((1,-1),(440,(0,1))),((1,4),(244,(0,0))),((2,0),(248,(0,0))),((2,1),(251,(0,0))),((2,3),(254,(0,0))),((3,2),(255,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_78_checked : successorFastRowCheck layer7 row6_78 row6_78choice = true := by decide
def row6_79 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3)]
def row6_79choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(320,(1,0))),((0,-1),(165,(0,1))),((0,1),(128,(0,0))),((0,2),(225,(0,0))),((0,3),(239,(0,0))),((1,-1),(441,(0,1))),((1,4),(245,(0,0))),((2,0),(249,(0,0))),((2,1),(252,(0,0))),((2,2),(254,(0,0))),((2,4),(256,(0,0))),((3,3),(257,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_79_checked : successorFastRowCheck layer7 row6_79 row6_79choice = true := by decide
def Closure6C009rows : List (List GridPoint) := [row6_72,row6_73,row6_74,row6_75,row6_76,row6_77,row6_78,row6_79]
theorem Closure6C009_closed : ∀ row ∈ Closure6C009rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C009rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_72choice,row6_72_checked⟩
  · subst row
    exact ⟨row6_73choice,row6_73_checked⟩
  · subst row
    exact ⟨row6_74choice,row6_74_checked⟩
  · subst row
    exact ⟨row6_75choice,row6_75_checked⟩
  · subst row
    exact ⟨row6_76choice,row6_76_checked⟩
  · subst row
    exact ⟨row6_77choice,row6_77_checked⟩
  · subst row
    exact ⟨row6_78choice,row6_78_checked⟩
  · subst row
    exact ⟨row6_79choice,row6_79_checked⟩
end Polyomino57
