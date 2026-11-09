import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_112 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2)]
def row7_112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(905,(1,0))),((-1,1),(1571,(1,0))),((-1,2),(2159,(1,0))),((0,-1),(181,(0,1))),((0,3),(162,(0,0))),((1,0),(243,(0,0))),((1,1),(284,(0,0))),((1,3),(334,(0,0))),((2,1),(352,(0,0))),((2,4),(360,(0,0))),((3,1),(363,(0,0))),((3,3),(364,(0,0))),((4,2),(365,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_112_checked : successorFastRowCheck layer8 row7_112 row7_112choice = true := by decide
def row7_113 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3)]
def row7_113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(906,(1,0))),((-1,1),(1572,(1,0))),((-1,2),(2160,(1,0))),((0,-1),(182,(0,1))),((0,3),(163,(0,0))),((1,0),(244,(0,0))),((1,1),(285,(0,0))),((1,3),(335,(0,0))),((2,1),(353,(0,0))),((2,4),(361,(0,0))),((3,2),(364,(0,0))),((3,4),(366,(0,0))),((4,3),(367,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_113_checked : successorFastRowCheck layer8 row7_113 row7_113choice = true := by decide
def row7_114 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2)]
def row7_114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(907,(1,0))),((-1,1),(1573,(1,0))),((-1,2),(2161,(1,0))),((0,-1),(183,(0,1))),((0,3),(164,(0,0))),((1,0),(245,(0,0))),((1,1),(286,(0,0))),((1,3),(336,(0,0))),((2,1),(355,(0,0))),((2,3),(363,(0,0))),((3,0),(368,(0,0))),((3,3),(369,(0,0))),((4,1),(370,(0,0))),((4,2),(371,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_114_checked : successorFastRowCheck layer8 row7_114 row7_114choice = true := by decide
def row7_115 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3)]
def row7_115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(908,(1,0))),((-1,1),(1574,(1,0))),((-1,2),(2162,(1,0))),((0,-1),(184,(0,1))),((0,3),(165,(0,0))),((1,0),(246,(0,0))),((1,1),(287,(0,0))),((1,3),(337,(0,0))),((2,1),(357,(0,0))),((2,3),(364,(0,0))),((3,1),(369,(0,0))),((3,4),(372,(0,0))),((4,2),(373,(0,0))),((4,3),(374,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_115_checked : successorFastRowCheck layer8 row7_115 row7_115choice = true := by decide
def row7_116 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2)]
def row7_116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(909,(1,0))),((-1,1),(1575,(1,0))),((-1,2),(2163,(1,0))),((0,-1),(185,(0,1))),((0,3),(166,(0,0))),((1,0),(247,(0,0))),((1,1),(288,(0,0))),((1,3),(338,(0,0))),((2,1),(358,(0,0))),((2,3),(365,(0,0))),((3,1),(371,(0,0))),((3,3),(373,(0,0))),((4,1),(375,(0,0))),((4,3),(376,(0,0))),((5,2),(377,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_116_checked : successorFastRowCheck layer8 row7_116 row7_116choice = true := by decide
def row7_117 : List GridPoint := [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3)]
def row7_117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(910,(1,0))),((-1,1),(1576,(1,0))),((-1,3),(2497,(1,0))),((-1,4),(2668,(1,0))),((0,-1),(186,(0,1))),((0,2),(47,(0,0))),((0,5),(378,(0,0))),((1,0),(379,(0,0))),((1,4),(380,(0,0))),((2,1),(381,(0,0))),((2,2),(382,(0,0))),((2,3),(383,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_117_checked : successorFastRowCheck layer8 row7_117 row7_117choice = true := by decide
def row7_118 : List GridPoint := [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3)]
def row7_118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(911,(1,0))),((-1,1),(1577,(1,0))),((-1,3),(2498,(1,0))),((0,-1),(188,(0,1))),((0,2),(82,(0,0))),((0,4),(379,(0,0))),((1,-1),(1249,(0,1))),((1,4),(384,(0,0))),((2,0),(385,(0,0))),((2,1),(386,(0,0))),((2,2),(387,(0,0))),((2,3),(388,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_118_checked : successorFastRowCheck layer8 row7_118 row7_118choice = true := by decide
def row7_119 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4)]
def row7_119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(912,(1,0))),((-1,1),(1578,(1,0))),((-1,3),(2499,(1,0))),((0,-1),(189,(0,1))),((0,2),(119,(0,0))),((0,4),(380,(0,0))),((1,0),(384,(0,0))),((1,5),(389,(0,0))),((2,1),(390,(0,0))),((2,2),(391,(0,0))),((2,3),(392,(0,0))),((2,4),(393,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_119_checked : successorFastRowCheck layer8 row7_119 row7_119choice = true := by decide
def Closure7C014rows : List (List GridPoint) := [row7_112,row7_113,row7_114,row7_115,row7_116,row7_117,row7_118,row7_119]
theorem Closure7C014_closed : ∀ row ∈ Closure7C014rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C014rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_112choice,row7_112_checked⟩
  · subst row
    exact ⟨row7_113choice,row7_113_checked⟩
  · subst row
    exact ⟨row7_114choice,row7_114_checked⟩
  · subst row
    exact ⟨row7_115choice,row7_115_checked⟩
  · subst row
    exact ⟨row7_116choice,row7_116_checked⟩
  · subst row
    exact ⟨row7_117choice,row7_117_checked⟩
  · subst row
    exact ⟨row7_118choice,row7_118_checked⟩
  · subst row
    exact ⟨row7_119choice,row7_119_checked⟩
end Polyomino57
