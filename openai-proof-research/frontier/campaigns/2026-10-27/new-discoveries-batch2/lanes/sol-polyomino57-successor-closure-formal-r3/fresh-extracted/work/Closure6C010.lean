import Layer7
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row6_80 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1)]
def row6_80choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(321,(1,0))),((0,-1),(167,(0,1))),((0,1),(129,(0,0))),((0,2),(226,(0,0))),((1,-1),(446,(0,1))),((1,3),(247,(0,0))),((2,-1),(506,(0,1))),((2,2),(258,(0,0))),((3,0),(259,(0,0))),((3,1),(260,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_80_checked : successorFastRowCheck layer7 row6_80 row6_80choice = true := by decide
def row6_81 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2)]
def row6_81choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(322,(1,0))),((0,-1),(168,(0,1))),((0,1),(130,(0,0))),((0,2),(227,(0,0))),((1,-1),(447,(0,1))),((1,3),(248,(0,0))),((2,-1),(507,(0,1))),((2,1),(258,(0,0))),((2,3),(261,(0,0))),((3,0),(262,(0,0))),((3,2),(263,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_81_checked : successorFastRowCheck layer7 row6_81 row6_81choice = true := by decide
def row6_82 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0)]
def row6_82choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(323,(1,0))),((0,-1),(169,(0,1))),((0,1),(131,(0,0))),((0,2),(228,(0,0))),((1,-1),(448,(0,1))),((1,3),(250,(0,0))),((2,-1),(509,(0,1))),((2,1),(259,(0,0))),((2,2),(262,(0,0))),((3,-1),(510,(0,1))),((3,1),(264,(0,0))),((4,0),(265,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_82_checked : successorFastRowCheck layer7 row6_82 row6_82choice = true := by decide
def row6_83 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2)]
def row6_83choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(324,(1,0))),((0,-1),(170,(0,1))),((0,1),(132,(0,0))),((0,2),(229,(0,0))),((1,-1),(449,(0,1))),((1,3),(251,(0,0))),((2,0),(258,(0,0))),((2,3),(266,(0,0))),((3,1),(267,(0,0))),((3,2),(268,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_83_checked : successorFastRowCheck layer7 row6_83 row6_83choice = true := by decide
def row6_84 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1)]
def row6_84choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(325,(1,0))),((0,-1),(171,(0,1))),((0,1),(133,(0,0))),((0,2),(230,(0,0))),((1,-1),(450,(0,1))),((1,3),(253,(0,0))),((2,0),(260,(0,0))),((2,2),(267,(0,0))),((3,0),(269,(0,0))),((3,2),(270,(0,0))),((4,1),(271,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_84_checked : successorFastRowCheck layer7 row6_84 row6_84choice = true := by decide
def row6_85 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3)]
def row6_85choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(326,(1,0))),((0,-1),(172,(0,1))),((0,1),(134,(0,0))),((0,2),(231,(0,0))),((1,-1),(451,(0,1))),((1,3),(254,(0,0))),((2,0),(261,(0,0))),((2,1),(266,(0,0))),((2,4),(272,(0,0))),((3,2),(273,(0,0))),((3,3),(274,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_85_checked : successorFastRowCheck layer7 row6_85 row6_85choice = true := by decide
def row6_86 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2)]
def row6_86choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(327,(1,0))),((0,-1),(173,(0,1))),((0,1),(135,(0,0))),((0,2),(232,(0,0))),((1,-1),(452,(0,1))),((1,3),(255,(0,0))),((2,0),(263,(0,0))),((2,1),(268,(0,0))),((2,3),(273,(0,0))),((3,1),(275,(0,0))),((3,3),(276,(0,0))),((4,2),(277,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_86_checked : successorFastRowCheck layer7 row6_86 row6_86choice = true := by decide
def row6_87 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2)]
def row6_87choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(328,(1,0))),((0,-1),(177,(0,1))),((0,1),(136,(0,0))),((1,-1),(461,(0,1))),((1,2),(258,(0,0))),((2,-1),(511,(0,1))),((2,3),(279,(0,0))),((3,0),(280,(0,0))),((3,1),(281,(0,0))),((3,2),(282,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row6_87_checked : successorFastRowCheck layer7 row6_87 row6_87choice = true := by decide
def Closure6C010rows : List (List GridPoint) := [row6_80,row6_81,row6_82,row6_83,row6_84,row6_85,row6_86,row6_87]
theorem Closure6C010_closed : ∀ row ∈ Closure6C010rows, ∃ choice, successorFastRowCheck layer7 row choice = true := by
  intro row hr
  simp only [Closure6C010rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row6_80choice,row6_80_checked⟩
  · subst row
    exact ⟨row6_81choice,row6_81_checked⟩
  · subst row
    exact ⟨row6_82choice,row6_82_checked⟩
  · subst row
    exact ⟨row6_83choice,row6_83_checked⟩
  · subst row
    exact ⟨row6_84choice,row6_84_checked⟩
  · subst row
    exact ⟨row6_85choice,row6_85_checked⟩
  · subst row
    exact ⟨row6_86choice,row6_86_checked⟩
  · subst row
    exact ⟨row6_87choice,row6_87_checked⟩
end Polyomino57
