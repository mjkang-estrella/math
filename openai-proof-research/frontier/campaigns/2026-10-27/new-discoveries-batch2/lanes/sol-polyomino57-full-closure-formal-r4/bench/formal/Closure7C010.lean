import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_80 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4)]
def row7_80choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(873,(1,0))),((-1,1),(1539,(1,0))),((-1,2),(2127,(1,0))),((0,-1),(148,(0,1))),((0,3),(119,(0,0))),((0,4),(188,(0,0))),((1,0),(194,(0,0))),((1,5),(261,(0,0))),((2,1),(262,(0,0))),((2,2),(263,(0,0))),((2,3),(264,(0,0))),((2,4),(265,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_80_checked : successorFastRowCheck layer8 row7_80 row7_80choice = true := by decide
def row7_81 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1)]
def row7_81choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(874,(1,0))),((-1,1),(1540,(1,0))),((-1,2),(2128,(1,0))),((0,-1),(149,(0,1))),((0,3),(120,(0,0))),((1,0),(196,(0,0))),((1,4),(262,(0,0))),((2,0),(266,(0,0))),((2,2),(267,(0,0))),((2,3),(268,(0,0))),((3,1),(269,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_81_checked : successorFastRowCheck layer8 row7_81 row7_81choice = true := by decide
def row7_82 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2)]
def row7_82choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(875,(1,0))),((-1,1),(1541,(1,0))),((-1,2),(2129,(1,0))),((0,-1),(150,(0,1))),((0,3),(121,(0,0))),((1,0),(197,(0,0))),((1,4),(263,(0,0))),((2,1),(267,(0,0))),((2,3),(270,(0,0))),((3,2),(271,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_82_checked : successorFastRowCheck layer8 row7_82 row7_82choice = true := by decide
def row7_83 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3)]
def row7_83choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(876,(1,0))),((-1,1),(1542,(1,0))),((-1,2),(2130,(1,0))),((0,-1),(151,(0,1))),((0,3),(122,(0,0))),((1,0),(198,(0,0))),((1,4),(264,(0,0))),((2,1),(268,(0,0))),((2,2),(270,(0,0))),((2,4),(272,(0,0))),((3,3),(273,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_83_checked : successorFastRowCheck layer8 row7_83 row7_83choice = true := by decide
def row7_84 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1)]
def row7_84choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(877,(1,0))),((-1,1),(1543,(1,0))),((-1,2),(2131,(1,0))),((0,-1),(152,(0,1))),((0,3),(123,(0,0))),((1,0),(199,(0,0))),((1,3),(266,(0,0))),((2,-1),(1241,(0,1))),((2,2),(274,(0,0))),((3,0),(275,(0,0))),((3,1),(276,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_84_checked : successorFastRowCheck layer8 row7_84 row7_84choice = true := by decide
def row7_85 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2)]
def row7_85choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(878,(1,0))),((-1,1),(1544,(1,0))),((-1,2),(2132,(1,0))),((0,-1),(153,(0,1))),((0,3),(124,(0,0))),((1,0),(202,(0,0))),((1,3),(267,(0,0))),((2,0),(274,(0,0))),((2,3),(277,(0,0))),((3,1),(278,(0,0))),((3,2),(279,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_85_checked : successorFastRowCheck layer8 row7_85 row7_85choice = true := by decide
def row7_86 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1)]
def row7_86choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(879,(1,0))),((-1,1),(1545,(1,0))),((-1,2),(2133,(1,0))),((0,-1),(154,(0,1))),((0,3),(125,(0,0))),((1,0),(203,(0,0))),((1,3),(269,(0,0))),((2,0),(276,(0,0))),((2,2),(278,(0,0))),((3,0),(280,(0,0))),((3,2),(281,(0,0))),((4,1),(282,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_86_checked : successorFastRowCheck layer8 row7_86 row7_86choice = true := by decide
def row7_87 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3)]
def row7_87choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(880,(1,0))),((-1,1),(1546,(1,0))),((-1,2),(2134,(1,0))),((0,-1),(155,(0,1))),((0,3),(126,(0,0))),((1,0),(204,(0,0))),((1,3),(270,(0,0))),((2,1),(277,(0,0))),((2,4),(283,(0,0))),((3,2),(284,(0,0))),((3,3),(285,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_87_checked : successorFastRowCheck layer8 row7_87 row7_87choice = true := by decide
def Closure7C010rows : List (List GridPoint) := [row7_80,row7_81,row7_82,row7_83,row7_84,row7_85,row7_86,row7_87]
theorem Closure7C010_closed : ∀ row ∈ Closure7C010rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C010rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_80choice,row7_80_checked⟩
  · subst row
    exact ⟨row7_81choice,row7_81_checked⟩
  · subst row
    exact ⟨row7_82choice,row7_82_checked⟩
  · subst row
    exact ⟨row7_83choice,row7_83_checked⟩
  · subst row
    exact ⟨row7_84choice,row7_84_checked⟩
  · subst row
    exact ⟨row7_85choice,row7_85_checked⟩
  · subst row
    exact ⟨row7_86choice,row7_86_checked⟩
  · subst row
    exact ⟨row7_87choice,row7_87_checked⟩
end Polyomino57
