import Layer8
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
def row7_176 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1)]
def row7_176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(969,(1,0))),((-1,1),(1635,(1,0))),((0,-1),(332,(0,1))),((0,2),(276,(0,0))),((1,0),(430,(0,0))),((1,3),(544,(0,0))),((2,-1),(1390,(0,1))),((2,2),(569,(0,0))),((3,0),(571,(0,0))),((3,2),(573,(0,0))),((4,1),(574,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_176_checked : successorFastRowCheck layer8 row7_176 row7_176choice = true := by decide
def row7_177 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3)]
def row7_177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(970,(1,0))),((-1,1),(1636,(1,0))),((0,-1),(333,(0,1))),((0,2),(277,(0,0))),((1,0),(436,(0,0))),((1,3),(545,(0,0))),((2,0),(567,(0,0))),((2,4),(575,(0,0))),((3,1),(576,(0,0))),((3,2),(577,(0,0))),((3,3),(578,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_177_checked : successorFastRowCheck layer8 row7_177 row7_177choice = true := by decide
def row7_178 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1)]
def row7_178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(971,(1,0))),((-1,1),(1637,(1,0))),((0,-1),(334,(0,1))),((0,2),(278,(0,0))),((1,0),(437,(0,0))),((1,3),(546,(0,0))),((2,0),(569,(0,0))),((2,3),(576,(0,0))),((3,0),(579,(0,0))),((3,2),(580,(0,0))),((4,1),(581,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_178_checked : successorFastRowCheck layer8 row7_178 row7_178choice = true := by decide
def row7_179 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2)]
def row7_179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(972,(1,0))),((-1,1),(1638,(1,0))),((0,-1),(335,(0,1))),((0,2),(279,(0,0))),((1,0),(438,(0,0))),((1,3),(547,(0,0))),((2,0),(570,(0,0))),((2,3),(577,(0,0))),((3,1),(580,(0,0))),((3,3),(582,(0,0))),((4,2),(583,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_179_checked : successorFastRowCheck layer8 row7_179 row7_179choice = true := by decide
def row7_180 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1)]
def row7_180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(973,(1,0))),((-1,1),(1639,(1,0))),((0,-1),(336,(0,1))),((0,2),(280,(0,0))),((1,0),(439,(0,0))),((1,3),(551,(0,0))),((2,0),(571,(0,0))),((2,2),(579,(0,0))),((3,-1),(1392,(0,1))),((3,2),(584,(0,0))),((4,0),(585,(0,0))),((4,1),(586,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_180_checked : successorFastRowCheck layer8 row7_180 row7_180choice = true := by decide
def row7_181 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2)]
def row7_181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(974,(1,0))),((-1,1),(1640,(1,0))),((0,-1),(337,(0,1))),((0,2),(281,(0,0))),((1,0),(440,(0,0))),((1,3),(552,(0,0))),((2,0),(573,(0,0))),((2,2),(580,(0,0))),((3,0),(584,(0,0))),((3,3),(587,(0,0))),((4,1),(588,(0,0))),((4,2),(589,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_181_checked : successorFastRowCheck layer8 row7_181 row7_181choice = true := by decide
def row7_182 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1)]
def row7_182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(975,(1,0))),((-1,1),(1641,(1,0))),((0,-1),(338,(0,1))),((0,2),(282,(0,0))),((1,0),(441,(0,0))),((1,3),(553,(0,0))),((2,0),(574,(0,0))),((2,2),(581,(0,0))),((3,0),(586,(0,0))),((3,2),(588,(0,0))),((4,0),(590,(0,0))),((4,2),(591,(0,0))),((5,1),(592,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_182_checked : successorFastRowCheck layer8 row7_182 row7_182choice = true := by decide
def row7_183 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4)]
def row7_183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(976,(1,0))),((-1,1),(1642,(1,0))),((0,-1),(339,(0,1))),((0,2),(283,(0,0))),((1,0),(442,(0,0))),((1,3),(554,(0,0))),((1,4),(566,(0,0))),((2,1),(575,(0,0))),((2,5),(593,(0,0))),((3,2),(594,(0,0))),((3,3),(595,(0,0))),((3,4),(596,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem row7_183_checked : successorFastRowCheck layer8 row7_183 row7_183choice = true := by decide
def Closure7C022rows : List (List GridPoint) := [row7_176,row7_177,row7_178,row7_179,row7_180,row7_181,row7_182,row7_183]
theorem Closure7C022_closed : ∀ row ∈ Closure7C022rows, ∃ choice, successorFastRowCheck layer8 row choice = true := by
  intro row hr
  simp only [Closure7C022rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst row
    exact ⟨row7_176choice,row7_176_checked⟩
  · subst row
    exact ⟨row7_177choice,row7_177_checked⟩
  · subst row
    exact ⟨row7_178choice,row7_178_checked⟩
  · subst row
    exact ⟨row7_179choice,row7_179_checked⟩
  · subst row
    exact ⟨row7_180choice,row7_180_checked⟩
  · subst row
    exact ⟨row7_181choice,row7_181_checked⟩
  · subst row
    exact ⟨row7_182choice,row7_182_checked⟩
  · subst row
    exact ⟨row7_183choice,row7_183_checked⟩
end Polyomino57
