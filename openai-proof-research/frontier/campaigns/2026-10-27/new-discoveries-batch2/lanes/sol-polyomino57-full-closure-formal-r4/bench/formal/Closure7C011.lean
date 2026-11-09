import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_88 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2)]
def row7_88choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(881,(1,0))),((-1,1),(1547,(1,0))),((-1,2),(2135,(1,0))),((0,-1),(156,(0,1))),((0,3),(127,(0,0))),((1,0),(205,(0,0))),((1,3),(271,(0,0))),((2,1),(279,(0,0))),((2,3),(284,(0,0))),((3,1),(286,(0,0))),((3,3),(287,(0,0))),((4,2),(288,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_88_checked : successorFastRowCheck layer8 row7_88 row7_88choice = true := by decide
def row7_89 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2)]
def row7_89choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(882,(1,0))),((-1,1),(1548,(1,0))),((-1,2),(2136,(1,0))),((0,-1),(158,(0,1))),((0,3),(139,(0,0))),((1,0),(206,(0,0))),((1,2),(274,(0,0))),((2,-1),(1242,(0,1))),((2,3),(290,(0,0))),((3,0),(291,(0,0))),((3,1),(292,(0,0))),((3,2),(293,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_89_checked : successorFastRowCheck layer8 row7_89 row7_89choice = true := by decide
def row7_90 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0)]
def row7_90choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(883,(1,0))),((-1,1),(1549,(1,0))),((-1,2),(2137,(1,0))),((0,-1),(159,(0,1))),((0,3),(140,(0,0))),((1,0),(207,(0,0))),((1,2),(275,(0,0))),((2,-1),(1244,(0,1))),((2,2),(291,(0,0))),((3,-1),(1246,(0,1))),((3,1),(294,(0,0))),((4,0),(295,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_90_checked : successorFastRowCheck layer8 row7_90 row7_90choice = true := by decide
def row7_91 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1)]
def row7_91choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(884,(1,0))),((-1,1),(1550,(1,0))),((-1,2),(2138,(1,0))),((0,-1),(160,(0,1))),((0,3),(141,(0,0))),((1,0),(208,(0,0))),((1,2),(276,(0,0))),((2,-1),(1245,(0,1))),((2,2),(292,(0,0))),((3,0),(294,(0,0))),((3,2),(296,(0,0))),((4,1),(297,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_91_checked : successorFastRowCheck layer8 row7_91 row7_91choice = true := by decide
def row7_92 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3)]
def row7_92choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(885,(1,0))),((-1,1),(1551,(1,0))),((-1,2),(2139,(1,0))),((0,-1),(161,(0,1))),((0,3),(142,(0,0))),((1,0),(211,(0,0))),((1,2),(277,(0,0))),((1,3),(289,(0,0))),((2,0),(290,(0,0))),((2,4),(298,(0,0))),((3,1),(299,(0,0))),((3,2),(300,(0,0))),((3,3),(301,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_92_checked : successorFastRowCheck layer8 row7_92 row7_92choice = true := by decide
def row7_93 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1)]
def row7_93choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(886,(1,0))),((-1,1),(1552,(1,0))),((-1,2),(2140,(1,0))),((0,-1),(162,(0,1))),((0,3),(143,(0,0))),((1,0),(212,(0,0))),((1,2),(278,(0,0))),((2,0),(292,(0,0))),((2,3),(299,(0,0))),((3,0),(302,(0,0))),((3,2),(303,(0,0))),((4,1),(304,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_93_checked : successorFastRowCheck layer8 row7_93 row7_93choice = true := by decide
def row7_94 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2)]
def row7_94choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(887,(1,0))),((-1,1),(1553,(1,0))),((-1,2),(2141,(1,0))),((0,-1),(163,(0,1))),((0,3),(144,(0,0))),((1,0),(213,(0,0))),((1,2),(279,(0,0))),((2,0),(293,(0,0))),((2,3),(300,(0,0))),((3,1),(303,(0,0))),((3,3),(305,(0,0))),((4,2),(306,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_94_checked : successorFastRowCheck layer8 row7_94 row7_94choice = true := by decide
def row7_95 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1)]
def row7_95choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(888,(1,0))),((-1,1),(1554,(1,0))),((-1,2),(2142,(1,0))),((0,-1),(164,(0,1))),((0,3),(145,(0,0))),((1,0),(214,(0,0))),((1,2),(280,(0,0))),((2,0),(294,(0,0))),((2,2),(302,(0,0))),((3,-1),(1247,(0,1))),((3,2),(307,(0,0))),((4,0),(308,(0,0))),((4,1),(309,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_95_checked : successorFastRowCheck layer8 row7_95 row7_95choice = true := by decide
def Closure7C011rows : List (List GridPoint) := [row7_88,row7_89,row7_90,row7_91,row7_92,row7_93,row7_94,row7_95]
theorem Closure7C011_closed : ∀ row ∈ Closure7C011rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C011rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_88choice,row7_88_checked⟩
  · subst row
    exact ⟨row7_89choice,row7_89_checked⟩
  · subst row
    exact ⟨row7_90choice,row7_90_checked⟩
  · subst row
    exact ⟨row7_91choice,row7_91_checked⟩
  · subst row
    exact ⟨row7_92choice,row7_92_checked⟩
  · subst row
    exact ⟨row7_93choice,row7_93_checked⟩
  · subst row
    exact ⟨row7_94choice,row7_94_checked⟩
  · subst row
    exact ⟨row7_95choice,row7_95_checked⟩
end Polyomino57
